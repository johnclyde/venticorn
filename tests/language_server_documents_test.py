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

    def search(self, version=1, search_id=1):
        return self.session.request("acorn/search", {
            "uri": self.uri, "version": version, "selectedLine": 0, "id": search_id,
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


if __name__ == "__main__":
    unittest.main()
