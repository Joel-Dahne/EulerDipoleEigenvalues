#!/usr/bin/env python3
"""Run one Pi proof worker; keep its transcript out of the parent's context.

This is a POSIX convenience runner, not a sandbox. Review the resulting diff
and validate Lean independently, regardless of the worker's final report.
"""

import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
INSTRUCTIONS = ROOT / "docs/tooling/pi-proof-worker.md"


def summarize(events_path):
    """Count completed assistant responses once, not their streaming deltas."""
    usage = {key: 0 for key in ("input", "output", "cacheRead", "cacheWrite", "totalTokens")}
    turns, cost, final, stop_reason, error = 0, 0.0, "", None, None
    settled, aborted, malformed = False, False, 0
    models = set()
    with events_path.open() as stream:
        for line in stream:
            try:
                event = json.loads(line)
            except json.JSONDecodeError:
                malformed += 1
                continue
            if event.get("type") == "message_end":
                msg = event.get("message", {})
                if msg.get("role") != "assistant":
                    continue
                turns += 1
                model = msg.get("model")
                if model:
                    models.add(f"{msg.get('provider', '?')}/{model}")
                u = msg.get("usage", {})
                for key in usage:
                    usage[key] += u.get(key, 0) or 0
                cost += (u.get("cost") or {}).get("total", 0) or 0
                stop_reason = msg.get("stopReason")
                if msg.get("errorMessage"):
                    error = msg["errorMessage"]
                # Only the last completed response is the final report.
                final = "\n".join(block.get("text", "") for block in msg.get("content", [])
                                  if block.get("type") == "text")
            elif event.get("type") == "agent_settled":
                settled = True
                aborted = event.get("aborted", False)
    return {"turns": turns, "models": sorted(models), "usage": usage,
            "reported_cost": cost, "stop_reason": stop_reason, "error": error,
            "settled": settled, "aborted": aborted, "malformed_events": malformed,
            "report": final}


def terminate_group(proc):
    # Descendant tool processes may survive even if Pi itself has exited.
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    time.sleep(0.5)
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    proc.wait()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("task", type=Path, help="UTF-8 file containing the bounded proof task")
    parser.add_argument("--model", default="openai-codex/gpt-5.6-luna")
    parser.add_argument("--thinking", default="medium",
                        choices=["off", "minimal", "low", "medium", "high", "xhigh", "max"])
    parser.add_argument("--timeout", type=float, default=600, help="Wall-clock limit in seconds")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    task = args.task.resolve()
    if not task.is_file():
        parser.error(f"Task file not found: {task}")
    run = Path(tempfile.mkdtemp(prefix="pi-proof-worker-"))
    command = ["pi", "--mode", "json", "--no-session", "--no-context-files",
               "--no-skills", "--no-prompt-templates", "--no-extensions",
               "-e", "builtin:mcp", "-e", "builtin:codemode", "--approve",
               "--tools", "read,bash,edit,codemode,mcp__lean_lsp__*",
               "--exclude-tools", "mcp__lean_lsp__lean_build,mcp__lean_lsp__lean_multi_attempt",
               "--model", args.model, "--thinking", args.thinking,
               "--append-system-prompt", str(INSTRUCTIONS), "@" + str(task)]
    (run / "task.md").write_text(task.read_text())
    (run / "command.json").write_text(json.dumps(command, indent=2) + "\n")
    start = time.monotonic()
    print(f"Worker log directory: {run}", flush=True)
    reason = "completed"
    with (run / "events.jsonl").open("w") as stdout, (run / "stderr.log").open("w") as stderr:
        try:
            proc = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                                    stdout=stdout, stderr=stderr, start_new_session=True)
        except OSError as error:
            print(f"Could not start Pi: {error}; logs: {run}")
            return 1
        try:
            proc.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            reason = "timeout"
            terminate_group(proc)
        except KeyboardInterrupt:
            reason = "interrupted"
            terminate_group(proc)
        finally:
            if proc.poll() is None:
                terminate_group(proc)
    summary = summarize(run / "events.jsonl")
    summary.update(termination=reason, exit_code=proc.returncode,
                   elapsed_seconds=round(time.monotonic() - start, 2), log_directory=str(run))
    (run / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    # JSON mode can exit zero even on model errors: check events as well.
    ok = (reason == "completed" and proc.returncode == 0 and summary["settled"]
          and not summary["aborted"] and summary["stop_reason"] == "stop"
          and not summary["malformed_events"])
    if not ok:
        print(f"Worker did not finish normally; inspect {run / 'stderr.log'}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
