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
    "language_server.exe" if os.name == "nt" else "language_server"
)


class LanguageServerTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="venticorn-lsp-")
        self.addCleanup(self.directory.cleanup)
        self.library = Path(self.directory.name)
        (self.library / "example.ac").write_text("theorem identity { true }\n")
        self.environment = dict(os.environ, VENTICORN_LIBRARY=str(self.library))

    def initialize_and_shutdown(self, root_uri):
        with subprocess.Popen(
            [str(BINARY)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, env=self.environment,
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
                send({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
                    "processId": None, "rootUri": root_uri, "capabilities": {},
                }})
                self.assertIn("capabilities", receive(1)["result"])
                send({"jsonrpc": "2.0", "method": "initialized", "params": {}})
                send({"jsonrpc": "2.0", "id": 2, "method": "shutdown"})
                shutdown = receive(2)
                self.assertIn("result", shutdown, shutdown)
                self.assertIsNone(shutdown["result"])
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
        self.initialize_and_shutdown(self.library.as_uri())

    def test_initialize_without_workspace(self):
        self.initialize_and_shutdown(None)

    def test_missing_library_reports_error_without_protocol_output(self):
        self.environment["VENTICORN_LIBRARY"] = str(self.library / "missing")
        result = subprocess.run(
            [str(BINARY)], env=self.environment, input=b"", capture_output=True,
            timeout=10,
        )
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, b"")
        self.assertIn(b"VENTICORN_LIBRARY is not a directory", result.stderr)
        self.assertNotIn(b"panicked", result.stderr)


if __name__ == "__main__":
    unittest.main()
