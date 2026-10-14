// Modified for Venticorn.
// Saved text and the newest accepted editor version belong to the same document.
pub struct LiveDocument {
    text: String,
    live_version: i32,
    saved_version: i32,
}

impl LiveDocument {
    pub fn new(text: &str, version: i32) -> Self {
        Self {
            text: text.to_owned(),
            live_version: version,
            saved_version: version,
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }
    pub fn live_version(&self) -> i32 {
        self.live_version
    }
    pub fn saved_version(&self) -> i32 {
        self.saved_version
    }

    pub fn advance_version(&mut self, version: i32) -> Result<(), String> {
        if version <= self.live_version {
            return Err(format!(
                "version {} does not follow {}",
                version, self.live_version
            ));
        }
        self.live_version = version;
        Ok(())
    }

    pub fn save(&mut self, text: &str) -> i32 {
        self.text.clear();
        self.text.push_str(text);
        self.saved_version = self.live_version;
        self.saved_version
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn saves_use_latest_accepted_version() {
        let mut doc = LiveDocument::new("old", 7);
        doc.advance_version(9).unwrap();
        assert_eq!(doc.saved_version(), 7);
        assert_eq!(doc.save("new"), 9);
        assert_eq!(doc.text(), "new");
    }

    #[test]
    fn duplicate_and_older_versions_do_not_regress_document() {
        let mut doc = LiveDocument::new("old", 7);
        assert!(doc.advance_version(7).is_err());
        assert!(doc.advance_version(6).is_err());
        assert_eq!(doc.live_version(), 7);
        assert_eq!(doc.saved_version(), 7);
        assert_eq!(doc.text(), "old");
    }
}
