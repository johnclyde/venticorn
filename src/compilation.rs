// Modified for Venticorn: shared source-located compilation diagnostics.
use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::token::Token;

// Errors that happen during compilation.
// We will want to report these along with a location in the source code.
#[derive(Debug)]
pub struct Error {
    // The range of tokens the error occurred at.
    first_token: Token,
    last_token: Token,

    message: String,

    // When you try to import a module that itself had a compilation error, that is a "secondary error".
    // We may or may not want to report these.
    // If the primary location is visible, there's no point in also reporting the secondary.
    // But if the primary location is inaccessible, we should report it at the secondary location.
    pub secondary: bool,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "{}:", self.message)?;
        writeln!(f, "{}", self.first_token.line)?;
        let start = self.first_token.start as usize;
        let end = if self.first_token.line_number == self.last_token.line_number {
            (self.last_token.start + self.last_token.len) as usize
        } else {
            self.first_token.line.len()
        };
        let mut highlighted = false;
        // Token offsets are bytes. Terminal padding follows source characters,
        // while editor ranges use UTF-16 through the token position accessors.
        for (index, character) in self.first_token.line.char_indices() {
            if index < start {
                write!(f, "{}", if character == '\t' { '\t' } else { ' ' })?;
            } else if index < end {
                write!(f, "^")?;
                highlighted = true;
            } else {
                break;
            }
        }
        if !highlighted {
            // Empty lines and zero-length end-of-line tokens still need a marker.
            write!(f, "^")?;
        }
        writeln!(f)
    }
}

impl Error {
    pub fn new(first_token: &Token, last_token: &Token, message: &str) -> Self {
        Error {
            first_token: first_token.clone(),
            last_token: last_token.clone(),
            message: message.to_string(),
            secondary: false,
        }
    }

    pub fn secondary(first_token: &Token, last_token: &Token, message: &str) -> Self {
        Error {
            first_token: first_token.clone(),
            last_token: last_token.clone(),
            message: message.to_string(),
            secondary: true,
        }
    }

    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn range(&self) -> Range {
        Range::new(self.first_token.range().start, self.last_token.range().end)
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub trait ErrorSource {
    fn error(&self, message: &str) -> Error;
}
