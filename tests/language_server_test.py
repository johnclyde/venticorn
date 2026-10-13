"""Exercise the built language server through its actual stdio protocol."""

import json
import os
from pathlib import Path
import queue
import subprocess
import tempfile
import threading
import time
import unittest


ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / "target" / "debug" / (
    "venticornserver.exe" if os.name == "nt" else "venticornserver"
)


class LanguageServerTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="venticorn-lsp-")
        self.addCleanup(self.directory.cleanup)
        self.library = Path(self.directory.name)
        (self.library / "example.ac").write_text("theorem identity { true }\n")
        self.environment = dict(os.environ, VENTICORN_LIBRARY=str(self.library))

    def initialize_and_shutdown(
        self, root_uri, *, expected_error=None, cwd=None, initialize_params=None,
    ):
        with subprocess.Popen(
            [str(BINARY)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, env=self.environment, cwd=cwd,
        ) as process:
            responses = queue.Queue()
            errors = []

            def read_responses():
                try:
                    while True:
                        header = process.stdout.readline()
                        if not header:
                            responses.put(EOFError("language server closed stdout"))
                            return
                        if not header.lower().startswith(b"content-length:"):
                            raise ValueError(f"invalid LSP header: {header!r}")
                        length = int(header.split(b":", 1)[1])
                        while True:
                            line = process.stdout.readline()
                            if not line:
                                raise EOFError("language server exited inside a header")
                            if line == b"\r\n":
                                break
                        responses.put(json.loads(process.stdout.read(length)))
                except Exception as error:
                    responses.put(error)

            def read_errors():
                for line in process.stderr:
                    errors.append(line.decode())

            stdout_thread = threading.Thread(target=read_responses, daemon=True)
            stderr_thread = threading.Thread(target=read_errors, daemon=True)
            stdout_thread.start()
            stderr_thread.start()

            def send(message):
                payload = json.dumps(message).encode()
                process.stdin.write(
                    f"Content-Length: {len(payload)}\r\n\r\n".encode() + payload
                )
                process.stdin.flush()

            def receive(request_id):
                deadline = time.monotonic() + 10
                while True:
                    message = responses.get(timeout=max(0, deadline - time.monotonic()))
                    if isinstance(message, Exception):
                        raise message
                    if message.get("id") == request_id:
                        return message

            try:
                params = {
                    "processId": None, "rootUri": root_uri, "capabilities": {},
                }
                params.update(initialize_params or {})
                send({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": params})
                initialized = receive(1)
                if expected_error is None:
                    self.assertIn("capabilities", initialized["result"])
                    send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
                else:
                    self.assertIn("error", initialized, initialized)
                    self.assertEqual(initialized["error"]["code"], -32602)
                    self.assertIn(expected_error, initialized["error"]["message"])

                send({"jsonrpc": "2.0", "id": 2, "method": "acorn/progress", "params": {}})
                progress = receive(2)
                if expected_error is None:
                    self.assertEqual(progress["result"], {"done": 0, "total": 0})
                    send({"jsonrpc": "2.0", "id": 3, "method": "shutdown"})
                    shutdown = receive(3)
                    self.assertIn("result", shutdown, shutdown)
                    self.assertIsNone(shutdown["result"])
                else:
                    self.assertEqual(progress["error"]["code"], -32002)

                # An unsuccessful initialize leaves the server uninitialized, so
                # it must exit without a shutdown request in that case.
                send({"jsonrpc": "2.0", "method": "exit"})
                process.stdin.close()
                self.assertEqual(process.wait(timeout=10), 0)
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()
                stdout_thread.join(timeout=2)
                stderr_thread.join(timeout=2)
            return "".join(errors)

    def test_initialize_with_workspace(self):
        root = self.library.as_uri()
        stderr = self.initialize_and_shutdown(root)
        self.assertIn(f"initializing with root {root}", stderr)

    def test_initialize_without_workspace(self):
        stderr = self.initialize_and_shutdown(None)
        self.assertIn("initializing with no root", stderr)

    def test_workspace_discovery_ignores_the_server_working_directory(self):
        self.environment.pop("VENTICORN_LIBRARY")
        workspace = self.library / "venticorn-library"
        workspace.mkdir()
        unrelated = self.library / "unrelated"
        unrelated.mkdir()
        stderr = self.initialize_and_shutdown(workspace.as_uri(), cwd=unrelated)
        self.assertIn(f"initializing with root {workspace.as_uri()}", stderr)

    def test_workspace_folders_work_without_legacy_root_uri(self):
        self.environment.pop("VENTICORN_LIBRARY")
        workspace = self.library / "acornlib"
        workspace.mkdir()
        self.initialize_and_shutdown(None, initialize_params={
            "workspaceFolders": [{"uri": workspace.as_uri(), "name": "library"}],
        })

    def test_explicit_library_takes_precedence_over_remote_workspace(self):
        self.initialize_and_shutdown("https://example.invalid/workspace")

    def test_missing_workspace_library_does_not_fall_back_to_cwd(self):
        self.environment.pop("VENTICORN_LIBRARY")
        working = self.library / "working"
        (working / "venticorn-library").mkdir(parents=True)
        workspace = self.library / "workspace"
        workspace.mkdir()
        self.initialize_and_shutdown(
            workspace.as_uri(), cwd=working, expected_error="no library found from",
        )

    def test_missing_workspace_requires_explicit_library(self):
        self.environment.pop("VENTICORN_LIBRARY")
        self.initialize_and_shutdown(
            None, expected_error="open a workspace folder or set VENTICORN_LIBRARY",
        )

    def test_non_file_workspace_is_rejected_without_override(self):
        self.environment.pop("VENTICORN_LIBRARY")
        self.initialize_and_shutdown(
            "https://example.invalid/workspace",
            expected_error="workspace root is not a local file URI",
        )

    def test_missing_library_returns_initialize_error(self):
        self.environment["VENTICORN_LIBRARY"] = str(self.library / "missing")
        stderr = self.initialize_and_shutdown(
            self.library.as_uri(),
            expected_error="VENTICORN_LIBRARY is not a directory",
        )
        self.assertNotIn("panicked", stderr)

    def test_startup_does_not_require_a_library_before_initialize(self):
        self.environment["VENTICORN_LIBRARY"] = str(self.library / "missing")
        result = subprocess.run(
            [str(BINARY)], env=self.environment, input=b"", capture_output=True,
            timeout=10,
        )
        self.assertEqual(result.returncode, 0)
        self.assertEqual(result.stdout, b"")
        self.assertNotIn(b"panicked", result.stderr)


if __name__ == "__main__":
    unittest.main()
