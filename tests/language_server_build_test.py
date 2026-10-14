"""Build identity, document versions, and diagnostic publication over real LSP."""
import os
from pathlib import Path
import tempfile
import time
import unittest
from lsp_session import LspSession

ROOT = Path(__file__).resolve().parents[1]
BINARY = Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target")) / "debug" / (
    "venticornserver.exe" if os.name == "nt" else "venticornserver"
)

class BuildPublicationTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="venticorn-build-lsp-")
        self.addCleanup(self.directory.cleanup)
        root = Path(self.directory.name)
        library = root / "library"
        library.mkdir()
        self.uri = (root / "proof.ac").as_uri()
        self.other = (root / "other.ac").as_uri()
        self.session = LspSession(BINARY, dict(os.environ, VENTICORN_LIBRARY=str(library)))
        self.addCleanup(self.session.close)
        result = self.session.request("initialize", {"processId": None, "rootUri": None, "capabilities": {}})
        self.assertIn("capabilities", result["result"])
        self.session.notify("initialized", {})

    def open(self, text, version=1, uri=None):
        self.session.notify("textDocument/didOpen", {"textDocument": {
            "uri": uri or self.uri, "languageId": "acorn", "version": version, "text": text,
        }})

    def change(self, version, text):
        self.session.notify("textDocument/didChange", {
            "textDocument": {"uri": self.uri, "version": version}, "contentChanges": [{"text": text}],
        })

    def save(self, text):
        self.session.notify("textDocument/didSave", {"textDocument": {"uri": self.uri}, "text": text})

    def progress(self):
        return self.session.request("acorn/progress", {})["result"]

    def wait_for_build(self, previous=None, *, total=1):
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            progress = self.progress()
            if progress["buildId"] not in (None, previous) and progress["done"] == progress["total"] == total:
                return progress
            time.sleep(0.01)
        self.fail(f"build did not finish: {progress}; stderr={''.join(self.session.errors)}")

    def diagnostics(self, uri=None):
        return [message["params"] for message in self.session.notifications
                if message.get("method") == "textDocument/publishDiagnostics"
                and message["params"]["uri"] == (uri or self.uri)]

    def wait_for_diagnostic(self, predicate):
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            self.progress()
            values = self.diagnostics()
            if values and predicate(values[-1]):
                return values[-1]
            time.sleep(0.01)
        self.fail(f"expected diagnostic was not published: {values}")

    def test_edit_save_and_zero_goal_build_publish_current_versions(self):
        self.open("theorem impossible { false }\n", 3)
        old = self.wait_for_build()
        self.wait_for_diagnostic(lambda item: item["diagnostics"] and item.get("version") == 3)
        text = "theorem identity { true }\n"
        self.change(4, text)
        progress = self.progress()
        self.assertEqual(progress["buildId"], None)
        self.assertEqual(progress["docs"], {})
        self.wait_for_diagnostic(lambda item: item.get("version") == 4 and not item["diagnostics"])
        self.save(text)
        current = self.wait_for_build(old["buildId"])
        self.assertEqual(current["docs"][self.uri]["verified"], [0])
        self.assertEqual(current["docs"][self.uri]["version"], 4)
        self.change(5, "")
        self.save("")
        empty = self.wait_for_build(current["buildId"], total=0)
        self.assertEqual(empty["docs"][self.uri]["verified"], [])
        self.wait_for_diagnostic(lambda item: item.get("version") == 5 and not item["diagnostics"])

    def test_close_and_same_version_reopen_get_new_build_identity(self):
        self.open("theorem impossible { false }\n", 7)
        old = self.wait_for_build()
        self.session.notify("textDocument/didClose", {"textDocument": {"uri": self.uri}})
        closed = self.wait_for_diagnostic(lambda item: not item["diagnostics"] and item.get("version") is None)
        self.assertEqual(closed["diagnostics"], [])
        self.assertIsNone(closed.get("version"))
        first_new = len(self.session.notifications)
        self.open("theorem reopened { true }\n", 7)
        current = self.wait_for_build(old["buildId"])
        self.assertEqual(current["docs"][self.uri]["verified"], [0])
        later = self.session.notifications[first_new:]
        self.assertFalse(any(message.get("method") == "textDocument/publishDiagnostics"
                             and message["params"]["diagnostics"] for message in later))

    def test_build_does_not_mark_an_edited_unsaved_document_verified(self):
        self.open("theorem first { true }\n", 1)
        old = self.wait_for_build()
        self.change(2, "theorem changed { false }\n")
        self.open("theorem other { true }\n", 1, self.other)
        current = self.wait_for_build(old["buildId"], total=2)
        self.assertNotIn(self.uri, current["docs"])
        self.assertEqual(current["docs"][self.other], {"version": 1, "verified": [0]})
        self.wait_for_diagnostic(lambda item: item.get("version") == 2 and not item["diagnostics"])

    def test_unsaved_edit_keeps_other_saved_document_searchable(self):
        self.open("theorem first { true }\n")
        first = self.wait_for_build()
        text = "\n".join([
            "let a: Bool = axiom", "let b: Bool = axiom", "let c: Bool = axiom",
            "axiom first { a }", "axiom next { a -> b }", "axiom last { b -> c }",
            "theorem chain { c }", "",
        ])
        self.open(text, 1, self.other)
        self.wait_for_build(first["buildId"], total=2)
        self.change(2, "theorem changed { false }\n")
        edited = self.session.request("acorn/search", {
            "uri": self.uri, "version": 2, "selectedLine": 0, "id": 80,
        })["result"]
        self.assertTrue(edited["loading"])
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            result = self.session.request("acorn/search", {
                "uri": self.other, "version": 1, "selectedLine": 6, "id": 81,
            })["result"]
            self.assertIsNone(result["failure"])
            if result["status"]["outcome"] is not None:
                self.assertEqual(result["status"]["outcome"], "Success")
                return
            time.sleep(0.01)
        self.fail(f"unchanged saved-document search stayed pending: {result}")

    def test_a_superseded_busy_build_cannot_replace_the_latest_progress(self):
        busy = "\n".join(f"theorem claim{i} {{ true }}" for i in range(250))
        self.open(busy, 1)
        self.change(2, "theorem latest { true }\n")
        self.save("theorem latest { true }\n")
        current = self.wait_for_build()
        self.assertEqual(current["docs"][self.uri]["verified"], [0])
        for _ in range(3):
            self.assertEqual(self.progress(), current)
        self.wait_for_diagnostic(lambda item: item.get("version") == 2 and not item["diagnostics"])

if __name__ == "__main__":
    unittest.main()
