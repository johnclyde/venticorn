// Modified for Venticorn.
use tower_lsp::lsp_types::{Position, TextDocumentContentChangeEvent};

// The exact editor text and its saved-line identities, independent of the project snapshot.
pub struct LiveDocument {
    text: String,
    lines: Vec<LiveLine>,
    live_version: i32,
    saved_version: i32,
}

#[derive(Clone)]
struct LiveLine {
    start: usize,
    content_end: usize,
    end: usize,
    // None after any part of this line is touched, until the next save.
    saved_index: Option<u32>,
}

// Retain all bytes, including CRLF, lone CR, and the final empty line.
fn split_lines(text: &str, saved: bool) -> Vec<LiveLine> {
    let bytes = text.as_bytes();
    let mut lines = Vec::new();
    let mut start = 0;
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'\r' || bytes[index] == b'\n' {
            let content_end = index;
            if bytes[index] == b'\r' && bytes.get(index + 1) == Some(&b'\n') {
                index += 1;
            }
            index += 1;
            lines.push(LiveLine {
                start,
                content_end,
                end: index,
                saved_index: saved.then_some(lines.len() as u32),
            });
            start = index;
        } else {
            index += 1;
        }
    }
    lines.push(LiveLine {
        start,
        content_end: text.len(),
        end: text.len(),
        saved_index: saved.then_some(lines.len() as u32),
    });
    lines
}

fn byte_offset(text: &str, lines: &[LiveLine], position: Position) -> Result<usize, String> {
    let line = lines
        .get(position.line as usize)
        .ok_or_else(|| format!("line {} is outside the document", position.line))?;
    let mut character = 0;
    for (offset, scalar) in text[line.start..line.content_end].char_indices() {
        if character == position.character {
            return Ok(line.start + offset);
        }
        character += scalar.len_utf16() as u32;
        if character > position.character {
            return Err("position splits a UTF-16 surrogate pair".into());
        }
    }
    if character == position.character {
        Ok(line.content_end)
    } else {
        Err(format!(
            "character {} is outside line {}",
            position.character, position.line
        ))
    }
}

impl LiveDocument {
    pub fn new(text: &str, version: i32) -> Self {
        Self {
            text: text.to_owned(),
            lines: split_lines(text, true),
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

    pub fn line_text(&self, line: u32) -> Option<&str> {
        self.lines
            .get(line as usize)
            .map(|line| &self.text[line.start..line.content_end])
    }

    // LSP columns count UTF-16 code units, not bytes or Unicode scalars.
    pub fn get_prefix(&self, line: u32, character: u32) -> Option<String> {
        let start = self.byte_offset(Position::new(line, 0)).ok()?;
        let end = self.byte_offset(Position::new(line, character)).ok()?;
        self.text.get(start..end).map(str::to_string)
    }

    pub fn saved_line(&self, line: u32) -> Option<u32> {
        self.lines
            .get(line as usize)
            .and_then(|line| line.saved_index)
    }

    pub fn byte_offset(&self, position: Position) -> Result<usize, String> {
        byte_offset(&self.text, &self.lines, position)
    }

    // LSP changes in one notification are sequential, but the notification commits atomically.
    // Validation failures must leave text, version, and saved-line identity untouched.
    pub fn apply_changes(
        &mut self,
        changes: &[TextDocumentContentChangeEvent],
        version: i32,
    ) -> Result<(), String> {
        if version <= self.live_version {
            return Err(format!(
                "version {} does not follow {}",
                version, self.live_version
            ));
        }
        if changes.is_empty() {
            return Err("change notification contains no edits".into());
        }
        let mut text = self.text.clone();
        let mut lines = self.lines.clone();
        for change in changes {
            let range = match change.range {
                Some(range) => range,
                None => {
                    text.clone_from(&change.text);
                    lines = split_lines(&text, false);
                    continue;
                }
            };
            if (range.start.line, range.start.character) > (range.end.line, range.end.character) {
                return Err("edit range ends before it starts".into());
            }
            let start = byte_offset(&text, &lines, range.start)?;
            let end = byte_offset(&text, &lines, range.end)?;
            if let Some(length) = change.range_length {
                if text[start..end].encode_utf16().count() != length as usize {
                    return Err("rangeLength does not match the replaced UTF-16 text".into());
                }
            }
            text.replace_range(start..end, &change.text);
            let mut updated = split_lines(&text, false);
            for (index, old) in lines.iter().enumerate() {
                let mapped = if index < range.start.line as usize {
                    Some((old.start, old.end))
                } else if index > range.end.line as usize {
                    // This line follows the removed span, so these differences cannot underflow.
                    Some((
                        old.start - (end - start) + change.text.len(),
                        old.end - (end - start) + change.text.len(),
                    ))
                } else {
                    None
                };
                if let Some((start, end)) = mapped {
                    if let Ok(index) = updated.binary_search_by_key(&start, |line| line.start) {
                        // A change can merge CR and LF across a boundary. Keep identity only
                        // when the whole untouched line still has its original boundaries.
                        if updated[index].end == end {
                            updated[index].saved_index = old.saved_index;
                        }
                    }
                }
            }
            lines = updated;
        }
        self.text = text;
        self.lines = lines;
        self.live_version = version;
        Ok(())
    }

    // Saving acknowledges the current text; mismatched/stale save contents are rejected.
    pub fn save(&mut self, text: &str) -> Result<i32, String> {
        if self.text != text {
            return Err("saved text does not match the current document".into());
        }
        for (index, line) in self.lines.iter_mut().enumerate() {
            line.saved_index = Some(index as u32);
        }
        self.saved_version = self.live_version;
        Ok(self.saved_version)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tower_lsp::lsp_types::Range;

    fn edit(start: (u32, u32), end: (u32, u32), text: &str) -> TextDocumentContentChangeEvent {
        TextDocumentContentChangeEvent {
            range: Some(Range::new(
                Position::new(start.0, start.1),
                Position::new(end.0, end.1),
            )),
            range_length: None,
            text: text.into(),
        }
    }

    #[test]
    fn completion_prefixes_validate_utf16_and_line_boundaries() {
        let doc = LiveDocument::new("a😀é\r\ntext\n", 1);
        assert_eq!(doc.get_prefix(0, 3).as_deref(), Some("a😀"));
        assert_eq!(doc.get_prefix(0, 4).as_deref(), Some("a😀é"));
        assert_eq!(doc.get_prefix(1, 2).as_deref(), Some("te"));
        assert_eq!(doc.get_prefix(2, 0).as_deref(), Some(""));
        assert_eq!(doc.get_prefix(0, 2), None);
        assert_eq!(doc.get_prefix(0, 5), None);
        assert_eq!(doc.get_prefix(u32::MAX, 0), None);
    }

    #[test]
    fn unicode_edits_use_utf16_and_preserve_exact_line_endings() {
        let mut doc = LiveDocument::new("a😀é\r\nz\n", 1);
        doc.apply_changes(&[edit((0, 1), (0, 3), "𐐀")], 2).unwrap();
        assert_eq!(doc.text(), "a𐐀é\r\nz\n");
        assert_eq!(doc.line_text(0), Some("a𐐀é"));
        assert_eq!(doc.line_text(2), Some(""));
        assert_eq!(doc.saved_line(0), None);
        assert_eq!(doc.saved_line(1), Some(1));
        assert_eq!(doc.saved_line(2), Some(2));
        assert_eq!(doc.byte_offset(Position::new(0, 3)).unwrap(), 5);
    }

    #[test]
    fn sequential_edits_commit_as_one_version() {
        let mut doc = LiveDocument::new("ab\r\ncd\r\nef", 10);
        doc.apply_changes(
            &[edit((0, 1), (1, 1), "x\n"), edit((1, 0), (1, 1), "YZ")],
            12,
        )
        .unwrap();
        assert_eq!(doc.text(), "ax\nYZ\r\nef");
        assert_eq!(doc.live_version(), 12);
        assert_eq!(doc.saved_version(), 10);
        assert_eq!(doc.saved_line(0), None);
        assert_eq!(doc.saved_line(1), None);
        assert_eq!(doc.saved_line(2), Some(2));
        assert_eq!(doc.save("ax\nYZ\r\nef").unwrap(), 12);
        assert_eq!(doc.saved_line(1), Some(1));
    }

    #[test]
    fn invalid_batches_leave_all_state_unchanged() {
        let invalid = [
            edit((0, 2), (0, 2), "x"), // Inside the emoji surrogate pair.
            edit((0, 8), (0, 8), "x"),
            edit((9, 0), (9, 0), "x"),
            edit((1, 0), (0, 1), "x"),
            edit((0, 3), (0, 1), "x"),
        ];
        for change in invalid {
            let mut doc = LiveDocument::new("a😀b\r\nlast", 4);
            assert!(doc
                .apply_changes(&[edit((1, 0), (1, 0), "new"), change], 5)
                .is_err());
            assert_eq!(doc.text(), "a😀b\r\nlast");
            assert_eq!(doc.live_version(), 4);
            assert_eq!(doc.saved_version(), 4);
            assert_eq!(doc.saved_line(1), Some(1));
        }
    }

    #[test]
    fn full_replacement_empty_text_and_trailing_lines_are_retained() {
        let mut doc = LiveDocument::new("old", 1);
        doc.apply_changes(
            &[TextDocumentContentChangeEvent {
                range: None,
                range_length: None,
                text: "".into(),
            }],
            2,
        )
        .unwrap();
        assert_eq!(doc.line_text(0), Some(""));
        assert_eq!(doc.saved_line(0), None);
        doc.apply_changes(&[edit((0, 0), (0, 0), "a\r\nb\rc\n")], 3)
            .unwrap();
        assert_eq!(doc.text(), "a\r\nb\rc\n");
        assert_eq!(doc.line_text(3), Some(""));
        assert_eq!(doc.line_text(4), None);
    }

    #[test]
    fn shifted_untouched_lines_keep_original_saved_identity() {
        let mut doc = LiveDocument::new("before\nchanged\nafter\n", 1);
        doc.apply_changes(&[edit((1, 0), (1, 0), "new\n")], 2)
            .unwrap();
        assert_eq!(doc.text(), "before\nnew\nchanged\nafter\n");
        assert_eq!(doc.saved_line(0), Some(0));
        assert_eq!(doc.saved_line(1), None);
        assert_eq!(doc.saved_line(2), None);
        assert_eq!(doc.saved_line(3), Some(2));
        assert_eq!(doc.saved_line(4), Some(3));
        doc.apply_changes(&[edit((1, 0), (3, 0), "")], 3).unwrap();
        assert_eq!(doc.text(), "before\nafter\n");
        assert_eq!(doc.saved_line(1), None);
        assert_eq!(doc.saved_line(2), Some(3));
    }

    #[test]
    fn boundary_merging_does_not_misindex_untouched_lines() {
        let mut doc = LiveDocument::new("a\rb\nc", 1);
        doc.apply_changes(&[edit((1, 0), (1, 0), "\n")], 2).unwrap();
        assert_eq!(doc.text(), "a\r\nb\nc");
        assert_eq!(doc.saved_line(0), None);
        assert_eq!(doc.saved_line(1), None);
        assert_eq!(doc.saved_line(2), Some(2));
    }

    #[test]
    fn all_fixture_ranges_match_byte_splicing_and_keep_valid_line_identity() {
        let original = "a😀\r\nb\n";
        // Independently tabulated scalar boundaries: (LSP line, UTF-16 column, byte offset).
        let positions = [
            (0, 0, 0),
            (0, 1, 1),
            (0, 3, 5),
            (1, 0, 7),
            (1, 1, 8),
            (2, 0, 9),
        ];
        let saved = LiveDocument::new(original, 1);
        for (index, &(sl, sc, start)) in positions.iter().enumerate() {
            for &(el, ec, end) in &positions[index..] {
                for replacement in ["", "é", "\n", "\r", "\r\n", "x\nz"] {
                    let mut doc = LiveDocument::new(original, 1);
                    doc.apply_changes(&[edit((sl, sc), (el, ec), replacement)], 2)
                        .unwrap();
                    assert_eq!(
                        doc.text(),
                        format!("{}{}{}", &original[..start], replacement, &original[end..])
                    );
                    let mut previous = None;
                    for line in 0..doc.lines.len() as u32 {
                        if let Some(old) = doc.saved_line(line) {
                            assert_eq!(doc.line_text(line), saved.line_text(old));
                            assert!(previous.map_or(true, |prior| prior < old));
                            previous = Some(old);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn stale_versions_lengths_and_mismatched_saves_are_rejected() {
        let mut doc = LiveDocument::new("😀", 7);
        assert!(doc.apply_changes(&[edit((0, 0), (0, 2), "x")], 7).is_err());
        assert!(doc.apply_changes(&[edit((0, 0), (0, 2), "x")], 6).is_err());
        assert!(doc.apply_changes(&[], 8).is_err());
        let mut change = edit((0, 0), (0, 2), "x");
        change.range_length = Some(1);
        assert!(doc.apply_changes(&[change.clone()], 8).is_err());
        assert_eq!(doc.text(), "😀");
        change.range_length = Some(2);
        doc.apply_changes(&[change], 8).unwrap();
        assert!(doc.save("😀").is_err());
        assert_eq!(doc.saved_version(), 7);
        assert_eq!(doc.save("x").unwrap(), 8);
    }
}
