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

    def test_unsaved_local_prefixes_use_the_saved_proof_scope(self):
        source = "from nat import Nat, saved\nlet bar: Nat = saved\ntheorem goal<T>(bop: T) {\n bop = bop\n} by {\n \n}\n"
        self.open(source)
        self.change(2, (5, 1), (5, 1), "bo")
        self.assertEqual(self.complete(5, 3), ["bop"])
        self.change(3, (5, 1), (5, 3), "ba")
        self.assertEqual(self.complete(5, 3), ["bar"])
        self.change(4, (5, 1), (5, 3), "T")
        self.assertEqual(self.complete(5, 2), ["T"])

    def test_full_replacement_without_a_scope_anchor_is_conservative(self):
        self.open("from nat import Nat\nlet old: Nat = axiom\n")
        self.session.notify("textDocument/didChange", {
            "textDocument": {"uri": self.uri, "version": 2}, "contentChanges": [{"text": "ol"}],
        })
        self.assertEqual(self.complete(0, 2), [])
        self.session.notify("textDocument/didChange", {
            "textDocument": {"uri": self.uri, "version": 3}, "contentChanges": [{"text": "from nat import N"}],
        })
        self.assertEqual(self.complete(0, len("from nat import N")), ["Nat"])

    def test_unsaved_prefix_after_a_block_uses_the_parent_scope(self):
        self.open("theorem goal(hidden: Bool) {\n hidden or not hidden\n} by {\n true\n}\n\nlet later: Bool = axiom\nlet alias: Bool = later\n")
        self.change(2, (5, 0), (5, 0), "hid")
        self.assertEqual(self.complete(5, 3), [])
        self.change(3, (5, 0), (5, 3), "lat")
        self.assertEqual(self.complete(5, 3), [])
        self.change(4, (5, 0), (5, 3), "ali")
        self.assertEqual(self.complete(5, 3), [])

    def test_unsaved_member_and_module_prefixes_use_canonical_bindings(self):
        self.open("from nat import Nat, saved\nlet alias: Nat = saved\n\n")
        self.change(2, (2, 0), (2, 0), "alias.s")
        self.assertEqual(self.complete(2, 7), ["suc"])
        self.change(3, (2, 0), (2, 7), "(nat.N")
        self.assertEqual(self.complete(2, 6), ["Nat"])
        self.change(4, (2, 0), (2, 6), "// nat.N")
        self.assertEqual(self.complete(2, 8), [])

    def test_utf16_cursor_after_non_bmp_identifier_reads_the_exact_prefix(self):
        self.open("let a𐐨value: Bool = axiom\nlet saved: Bool = axiom\n\n")
        prefix = "a𐐨value and sav"
        self.change(2, (2, 0), (2, 0), prefix + "ed")
        column = len(prefix.encode("utf-16-le")) // 2
        self.assertEqual(self.complete(2, column), ["saved"], self.session.notifications + self.session.errors)
        self.assertEqual(self.complete(2, 2), [])

    def test_external_files_and_malformed_import_prefixes_stay_bounded(self):
        self.uri = self.library.parent.joinpath(self.library.name + "-external.ac").as_uri()
        self.open("from nat import Nat\n\n")
        previous = ""
        version = 2
        for prefix in ["Nat.s", "from ../nat import N", "from nat import Nat.s", "from nat import (N", "Nat..s", "from nat import Nat,sav"]:
            self.change(version, (1, 0), (1, len(previous)), prefix)
            expected = ["suc"] if prefix == "Nat.s" else (["saved"] if prefix.endswith(",sav") else [])
            self.assertEqual(self.complete(1, len(prefix)), expected)
            previous = prefix
            version += 1

    def test_unknown_documents_and_invalid_positions_have_no_candidates(self):
        self.open("from nat import Nat\n// a😀b\n")
        self.assertEqual(self.complete(1, 5), [])  # Inside the surrogate pair.
        self.assertEqual(self.complete(1, 100), [])
        self.assertEqual(self.complete(999, 0), [])
        self.assertEqual(self.complete(0, 1, "untitled:missing"), [])
        self.assertEqual(self.complete(0, 1, (self.library / "unopened.ac").as_uri()), [])


if __name__ == "__main__":
    unittest.main()
