"""Check completion candidates through the built server's actual stdio protocol."""

import os
from pathlib import Path
import tempfile
import unittest

from lsp_session import LspSession

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target")) / "debug" / (
    "venticornserver.exe" if os.name == "nt" else "venticornserver"
)


class CompletionTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="venticorn-completion-")
        self.addCleanup(self.directory.cleanup)
        self.library = Path(self.directory.name)
        (self.library / "nat.ac").write_text("inductive Nat {\n zero\n suc(Nat)\n}\nlet saved: Nat = axiom\n")
        self.uri = (self.library / "main.ac").as_uri()
        self.session = LspSession(BINARY, dict(os.environ, VENTICORN_LIBRARY=str(self.library)))
        self.addCleanup(self.session.close)
        response = self.session.request("initialize", {"processId": None, "rootUri": None, "capabilities": {}})
        self.assertIn("completionProvider", response["result"]["capabilities"])
        self.session.notify("initialized", {})

    def open(self, text="from nat import Nat\n", version=1):
        self.session.notify("textDocument/didOpen", {"textDocument": {
            "uri": self.uri, "languageId": "acorn", "version": version, "text": text,
        }})

    def complete(self, line, character, uri=None):
        response = self.session.request("textDocument/completion", {
            "textDocument": {"uri": uri or self.uri}, "position": {"line": line, "character": character},
        })
        self.assertNotIn("error", response)
        result = response["result"]
        if result is None:
            return []
        return [item["label"] for item in (result["items"] if isinstance(result, dict) else result)]

    def change(self, version, start, end, text):
        self.session.notify("textDocument/didChange", {
            "textDocument": {"uri": self.uri, "version": version},
            "contentChanges": [{"range": {
                "start": {"line": start[0], "character": start[1]},
                "end": {"line": end[0], "character": end[1]},
            }, "text": text}],
        })

    def test_import_completion_uses_the_prefix_at_the_cursor(self):
        self.open()
        self.assertEqual(self.complete(0, len("from nat import N")), ["Nat"])
        self.assertEqual(self.complete(0, len("from nat import Nat")), ["Nat"])

    def test_unknown_documents_and_invalid_positions_have_no_candidates(self):
        self.open("from nat import Nat\n// a😀b\n")
        self.assertEqual(self.complete(1, 5), [])  # Inside the surrogate pair.
        self.assertEqual(self.complete(1, 100), [])
        self.assertEqual(self.complete(999, 0), [])
        self.assertEqual(self.complete(0, 1, "untitled:missing"), [])
        self.assertEqual(self.complete(0, 1, (self.library / "unopened.ac").as_uri()), [])


if __name__ == "__main__":
    unittest.main()
