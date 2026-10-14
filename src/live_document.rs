// Modified for Venticorn.
// Saved text used by the project while the editor may have a newer live version.
pub struct LiveDocument {
    text: String,
    saved_version: i32,
}

impl LiveDocument {
    pub fn new(text: String, version: i32) -> Self {
        Self {
            text,
            saved_version: version,
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn saved_version(&self) -> i32 {
        self.saved_version
    }
}
