"""Exercise saved/live document identity through the real language server."""

import os
from pathlib import Path
import tempfile
import unittest

from lsp_session import LspSession

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target")) / "debug" / (
    "venticornserver.exe" if os.name == "nt" else "venticornserver"
)


class DocumentLifecycleTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="venticorn-documents-")
        self.addCleanup(self.directory.cleanup)
        root = Path(self.directory.name)
        library = root / "library"
        library.mkdir()
        self.uri = (root / "external.ac").as_uri()
        self.session = LspSession(BINARY, dict(os.environ, VENTICORN_LIBRARY=str(library)))
        self.addCleanup(self.session.close)
        response = self.session.request("initialize", {"processId": None, "rootUri": None, "capabilities": {}})
        self.assertIn("capabilities", response["result"])
        self.session.notify("initialized", {})

    def open(self, text="theorem first { true }\n", version=1):
        self.session.notify("textDocument/didOpen", {"textDocument": {
            "uri": self.uri, "languageId": "acorn", "version": version, "text": text,
        }})

    def change(self, version, text):
        self.session.notify("textDocument/didChange", {
            "textDocument": {"uri": self.uri, "version": version},
            "contentChanges": [{"text": text}],
        })

    def save(self, text):
        self.session.notify("textDocument/didSave", {
            "textDocument": {"uri": self.uri}, "text": text,
        })

    def search(self, version=1, search_id=1, line=0):
        return self.session.request("acorn/search", {
            "uri": self.uri, "version": version, "selectedLine": line, "id": search_id,
        })["result"]

    def close_document(self):
        self.session.notify("textDocument/didClose", {"textDocument": {"uri": self.uri}})

    def test_edit_invalidates_cached_search_and_info(self):
        self.open()
        first = self.search()
        self.assertIsNone(first["failure"])
        self.change(2, "theorem second { true }\n")
        self.assertIn("not current", self.search()["failure"])
        self.assertTrue(self.search(2)["loading"])
        info = self.session.request("acorn/info", {"searchId": 1, "clauseId": 0})["result"]
        self.assertIn("no search task", info["failure"])
        self.save("theorem second { true }\n")
        second = self.search(2, 2)
        self.assertEqual(second["version"], 2)
        self.assertIn("second", second["goalName"])

    def test_close_reopen_same_version_does_not_reuse_old_proof(self):
        self.open()
        self.assertIsNone(self.search()["failure"])
        self.close_document()
        self.assertIn("no text", self.search()["failure"])
        self.open("theorem reopened { true }\n")
        result = self.search(1, 2)
        self.assertEqual(result["id"], 2)
        self.assertIn("reopened", result["goalName"])

    def test_stale_changes_and_save_after_close_are_ignored(self):
        self.open(version=5)
        self.change(4, "theorem stale { false }\n")
        self.change(5, "theorem duplicate { false }\n")
        self.assertIn("first", self.search(5)["goalName"])
        self.close_document()
        self.save("theorem ghost { true }\n")
        self.assertIn("no text", self.search(5)["failure"])

    def edit_batch(self, version, changes):
        self.session.notify("textDocument/didChange", {
            "textDocument": {"uri": self.uri, "version": version},
            "contentChanges": changes,
        })

    @staticmethod
    def edit(line, start, end, text):
        return {"range": {
            "start": {"line": line, "character": start},
            "end": {"line": line, "character": end},
        }, "text": text}

    def tokens(self):
        return self.session.request("textDocument/semanticTokens/full", {
            "textDocument": {"uri": self.uri},
        })["result"]["data"]

    def test_unicode_edits_preserve_crlf_and_current_semantic_positions(self):
        self.open("// 😀\r\ntheorem first { true }\r\n")
        self.assertEqual(self.tokens()[:5], [0, 0, 5, 1, 0])
        self.edit_batch(2, [self.edit(0, 3, 5, "é"), self.edit(1, 8, 13, "second")])
        self.assertEqual(self.tokens()[:5], [0, 0, 4, 1, 0])
        self.save("// é\r\ntheorem second { true }\r\n")
        self.assertIn("second", self.search(2, 2, line=1)["goalName"])

    def test_invalid_edit_rolls_back_entire_notification_and_version(self):
        self.open("// 😀\r\ntheorem first { true }\r\n")
        self.edit_batch(2, [self.edit(1, 8, 13, "wrong"), self.edit(0, 4, 5, "x")])
        self.assertEqual(self.tokens()[:5], [0, 0, 5, 1, 0])
        self.assertIn("first", self.search(line=1)["goalName"])
        # The rejected notification did not consume version 2.
        self.edit_batch(2, [self.edit(1, 8, 13, "valid")])
        self.save("// 😀\r\ntheorem valid { true }\r\n")
        self.assertIn("valid", self.search(2, 2, line=1)["goalName"])

    def test_mismatched_save_cannot_commit_stale_text(self):
        self.open()
        self.change(2, "theorem current { true }\n")
        self.save("theorem first { true }\n")
        self.assertTrue(self.search(2)["loading"])
        self.save("theorem current { true }\n")
        self.assertIn("current", self.search(2)["goalName"])

    def test_full_replacement_then_ranged_edit_in_same_notification(self):
        self.open()
        self.edit_batch(2, [
            {"text": "theorem replacement { true }\n"},
            self.edit(0, 8, 19, "final"),
        ])
        self.save("theorem final { true }\n")
        self.assertIn("final", self.search(2)["goalName"])


if __name__ == "__main__":
    unittest.main()
