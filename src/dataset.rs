// Modified for Venticorn.

use std::fs::File;

use chrono::Local;
use ndarray::Array1;
use ndarray_npy::NpzWriter;

use crate::common;
use crate::features::Features;

// Training data from a verification run: each feature vector describes an activated proof step,
// and its label records whether that step was used in the proof.
pub struct Dataset {
    pub features: Vec<Features>,
    pub labels: Vec<bool>,
}

impl Dataset {
    pub fn new() -> Self {
        Dataset {
            features: vec![],
            labels: vec![],
        }
    }

    pub fn add(&mut self, features: Features, label: bool) {
        self.features.push(features);
        self.labels.push(label);
    }

    // Saves the dataset under files/datasets using the supplied filename.
    pub fn save_with_name(
        &self,
        relative_filename: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut d = common::files_dir();
        d.push("datasets");
        d.push(relative_filename);
        let file = File::create(d)?;
        let mut npz = NpzWriter::new(file);
        let features = Features::to_array2(&self.features);
        let labels = Array1::from(self.labels.clone());
        npz.add_array("features", &features)?;
        npz.add_array("labels", &labels)?;
        npz.finish()?;
        Ok(())
    }

    // Tags are a filename component, not a path. Keep generated names portable to Windows.
    fn tagged_filename(tag: &str) -> String {
        assert!(
            !tag.is_empty()
                && tag
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_'),
            "dataset tags must contain only ASCII letters, digits, hyphens or underscores"
        );
        format!(
            "{}-{}",
            tag,
            Local::now().format("%Y-%m-%d-%H-%M-%S-%f.npz")
        )
    }

    // Pick a tagged name and stop on a save error, like the default dataset save.
    pub fn save_with_tag(&self, tag: &str) {
        let filename = Self::tagged_filename(tag);
        println!(
            "Saving dataset with {} items to {}",
            self.features.len(),
            filename
        );
        self.save_with_name(&filename).unwrap();
    }

    pub fn save(&self) {
        self.save_with_tag("dataset");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ndarray::Array2;
    use ndarray_npy::NpzReader;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn tagged_save_preserves_feature_rows_and_labels() {
        let mut dataset = Dataset::new();
        for depth in [2, 7] {
            dataset.add(
                Features {
                    is_contradiction: false,
                    atom_count: 3,
                    is_counterfactual: false,
                    is_hypothetical: true,
                    is_factual: false,
                    is_assumption: false,
                    is_negated_goal: true,
                    proof_size: 5,
                    depth,
                },
                depth == 2,
            );
        }
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let tag = format!("roundtrip-{}-{}", std::process::id(), unique);
        dataset.save_with_tag(&tag);
        let directory = common::files_dir().join("datasets");
        let files: Vec<_> = std::fs::read_dir(directory)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| {
                path.file_name()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .starts_with(&tag)
            })
            .collect();
        assert_eq!(files.len(), 1);
        let bytes = std::fs::read(&files[0]).unwrap();
        std::fs::remove_file(&files[0]).unwrap();
        let mut npz = NpzReader::new(std::io::Cursor::new(bytes)).unwrap();
        let features: Array2<f32> = npz.by_name("features").unwrap();
        let labels: Array1<bool> = npz.by_name("labels").unwrap();
        assert_eq!(features, Features::to_array2(&dataset.features));
        assert_eq!(labels.to_vec(), vec![true, false]);
        let name = files[0].file_name().unwrap().to_str().unwrap();
        assert!(name.ends_with(".npz"));
        assert!(!name.contains(['<', '>', ':', '"', '/', '\\', '|', '?', '*']));
    }

    #[test]
    fn tagged_filenames_reject_paths_and_nonportable_characters() {
        for tag in [
            "",
            ".",
            "..",
            "../outside",
            "/absolute",
            "a\\b",
            "a:b",
            "a b",
            "a?",
        ] {
            assert!(std::panic::catch_unwind(|| Dataset::tagged_filename(tag)).is_err());
        }
        assert!(Dataset::tagged_filename("dataset-1_a").starts_with("dataset-1_a-"));
    }
}
