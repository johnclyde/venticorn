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

    def test_repeated_saved_source_keeps_full_ranges_and_changed_goal_is_not_replayed(self):
        text = "theorem full { true } by {\n true\n}\n"
        self.open(text, 1)
        first = self.wait_for_build(total=2)
        self.assertEqual(first["docs"][self.uri]["verified"], [[0, 2]])
        self.change(2, text)
        self.save(text)
        repeated = self.wait_for_build(first["buildId"], total=2)
        self.assertEqual(repeated["docs"][self.uri]["verified"], [[0, 2]])
        self.wait_for_diagnostic(lambda item: item.get("version") == 2 and not item["diagnostics"])
        changed = text.replace("full { true }", "full { false }")
        self.change(3, changed)
        self.save(changed)
        current = self.wait_for_build(repeated["buildId"], total=2)
        self.assertEqual(current["docs"][self.uri]["verified"], [[1, 1]])
        self.wait_for_diagnostic(lambda item: item.get("version") == 3 and item["diagnostics"])

    def test_constrained_structure_marks_include_the_body_and_reject_a_failed_subgoal(self):
        text = "structure Flag {\n value: Bool\n} constraint {\n value = value\n} by {\n true\n}\n"
        self.open(text)
        current = self.wait_for_build(total=2)
        deadline = time.monotonic() + 10
        while current["docs"].get(self.uri, {}).get("verified") != [[0, 6]]:
            self.assertLess(time.monotonic(), deadline, current)
            time.sleep(0.01)
            current = self.progress()
        selected = self.session.request("acorn/search", {
            "uri": self.uri, "version": 1, "selectedLine": 3, "id": 95,
        })["result"]
        self.assertIsNone(selected["failure"])
        self.assertIn("exists", selected["goalName"])
        bad = text.replace(" true\n", " false\n")
        self.change(2, bad)
        self.save(bad)
        self.wait_for_build(current["buildId"], total=2)
        self.wait_for_diagnostic(lambda item: item.get("version") == 2 and any(
            diagnostic["range"]["start"]["line"] == 5 for diagnostic in item["diagnostics"]))
        verified = self.progress()["docs"][self.uri]["verified"]
        self.assertNotIn([0, 6], verified)

    def test_compilation_diagnostics_use_utf16_columns(self):
        for version, (text, token) in enumerate([
            ("let x𐐀é: Bool = missing", "missing"),
            ("let x: Bool = y𐐀é", "y𐐀é"),
        ], 1):
            if version == 1:
                self.open(text, version)
            else:
                self.change(version, text)
                self.save(text)
            item = self.wait_for_diagnostic(lambda value: value.get("version") == version and value["diagnostics"])
            self.assertEqual(len(item["diagnostics"]), 1)
            diagnostic = item["diagnostics"][0]
            start = len(text[:text.index(token)].encode("utf-16-le")) // 2
            end = start + len(token.encode("utf-16-le")) // 2
            self.assertEqual(diagnostic["range"], {
                "start": {"line": 0, "character": start},
                "end": {"line": 0, "character": end},
            })
            self.assertIn("unknown identifier", diagnostic["message"])

    def test_empty_open_then_edit_and_save_gets_a_fresh_verification(self):
        self.open("", 1)
        empty = self.wait_for_build(total=0)
        text = "theorem ready { true }\n"
        self.change(2, text)
        self.assertIsNone(self.progress()["buildId"])
        params = {"uri": self.uri, "version": 2, "selectedLine": 0, "id": 90}
        self.assertTrue(self.session.request("acorn/search", params)["result"]["loading"])
        self.save(text)
        current = self.wait_for_build(empty["buildId"])
        self.assertNotEqual(current["buildId"], empty["buildId"])
        result = self.session.request("acorn/search", params)["result"]
        self.assertIsNone(result["failure"])
        self.assertIn("ready", result["goalName"])
        self.wait_for_diagnostic(lambda item: item.get("version") == 2 and not item["diagnostics"])
        self.change(3, "theorem changed { false }\n")
        self.assertIsNone(self.progress()["buildId"])

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
        self.assertEqual(current["docs"][self.uri]["verified"], [[0, 0]])
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
        self.assertEqual(current["docs"][self.uri]["verified"], [[0, 0]])
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
        self.assertEqual(current["docs"][self.other], {"version": 1, "verified": [[0, 0]]})
        self.wait_for_diagnostic(lambda item: item.get("version") == 2 and not item["diagnostics"])

    def test_failed_subgoal_does_not_mark_its_theorem_verified(self):
        self.open("theorem misleading { true } by {\n false\n}\n")
        current = self.wait_for_build(total=2)
        self.assertEqual(current["docs"][self.uri]["verified"], [])
        self.wait_for_diagnostic(lambda item: bool(item["diagnostics"]))

    def test_successful_theorem_collapses_its_subgoals_into_one_range(self):
        self.open("theorem complete { true } by {\n true\n}\n")
        current = self.wait_for_build(total=2)
        self.assertEqual(current["docs"][self.uri]["verified"], [[0, 2]])

    def test_failed_theorem_does_not_hide_a_separate_successful_theorem(self):
        self.open("theorem incomplete { true } by {\n false\n}\ntheorem complete { true }\n")
        current = self.wait_for_build(total=3)
        self.assertEqual(current["docs"][self.uri]["verified"], [[3, 3]])

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
        self.assertEqual(current["docs"][self.uri]["verified"], [[0, 0]])
        for _ in range(3):
            self.assertEqual(self.progress(), current)
        self.wait_for_diagnostic(lambda item: item.get("version") == 2 and not item["diagnostics"])

if __name__ == "__main__":
    unittest.main()
