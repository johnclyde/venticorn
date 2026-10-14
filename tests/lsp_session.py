"""A bounded stdio LSP session for integration regressions."""

import json
import queue
import subprocess
import threading
import time


class LspSession:
    def __init__(self, binary, environment, *, args=(), cwd=None):
        self.process = subprocess.Popen(
            [str(binary), *args], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, env=environment, cwd=cwd,
        )
        self.responses = queue.Queue()
        self.notifications = []
        self.errors = []
        self.next_id = 1
        self.threads = [
            threading.Thread(target=self._read, daemon=True),
            threading.Thread(target=self._read_errors, daemon=True),
        ]
        for thread in self.threads:
            thread.start()

    def _read(self):
        try:
            while True:
                line = self.process.stdout.readline()
                if not line:
                    raise EOFError("language server closed stdout")
                if not line.lower().startswith(b"content-length:"):
                    raise ValueError(f"invalid LSP header: {line!r}")
                length = int(line.split(b":", 1)[1])
                while True:
                    line = self.process.stdout.readline()
                    if not line:
                        raise EOFError("language server exited inside a header")
                    if line == b"\r\n":
                        break
                self.responses.put(json.loads(self.process.stdout.read(length)))
        except Exception as error:
            self.responses.put(error)

    def _read_errors(self):
        for line in self.process.stderr:
            self.errors.append(line.decode())

    def _send(self, message):
        payload = json.dumps(dict(jsonrpc="2.0", **message)).encode()
        self.process.stdin.write(f"Content-Length: {len(payload)}\r\n\r\n".encode() + payload)
        self.process.stdin.flush()

    def notify(self, method, params):
        self._send({"method": method, "params": params})

    def request(self, method, params=None):
        request_id = self.next_id
        self.next_id += 1
        self._send({"id": request_id, "method": method, "params": params})
        deadline = time.monotonic() + 10
        while True:
            message = self.responses.get(timeout=max(0, deadline - time.monotonic()))
            if isinstance(message, Exception):
                raise message
            if message.get("id") == request_id:
                return message
            self.notifications.append(message)

    def close(self):
        try:
            if self.process.poll() is None:
                self.request("shutdown")
                self.notify("exit", None)
                self.process.stdin.close()
                self.process.wait(timeout=10)
        finally:
            if self.process.poll() is None:
                self.process.kill()
                self.process.wait()
            for thread in self.threads:
                thread.join(timeout=2)
            for stream in (self.process.stdin, self.process.stdout, self.process.stderr):
                stream.close()
