#!/usr/bin/env python3
"""Run a bounded CAS job with a durable ledger and isolated process group.

Every job starts in a new POSIX session. Timeout and interrupt cleanup signal
only that recorded process group; this supervisor never discovers descendants
by walking the machine-wide PID tree.
"""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import sys
import time
from typing import IO, NoReturn, Sequence


EXIT_TIMEOUT = 124
EXIT_INTERRUPTED = 130
EXIT_SOURCE_CHANGED = 74
EXIT_DUPLICATE = 75
EXIT_SAFETY = 70


class JobInterrupted(Exception):
    """Raised by the signal handler so the main path owns all cleanup."""


def atomic_text(path: Path, value: str) -> None:
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    temporary.write_text(value)
    os.replace(temporary, path)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def pid_exists(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def group_exists(pgid: int) -> bool:
    try:
        os.killpg(pgid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def validate_owned_group(process: subprocess.Popen[bytes], pgid: int) -> None:
    """Fail closed unless the live child still leads the group we created."""

    if pgid <= 1 or pgid != process.pid:
        raise RuntimeError(f"unsafe process group identity: pid={process.pid} pgid={pgid}")
    try:
        current = os.getpgid(process.pid)
    except ProcessLookupError:
        process.poll()
        raise RuntimeError(
            "child disappeared before its isolated process group could be validated; "
            "refusing to signal any PGID"
        )
    if current != pgid:
        raise RuntimeError(
            f"child left its isolated process group: pid={process.pid} expected={pgid} actual={current}"
        )


def stop_owned_group(process: subprocess.Popen[bytes], pgid: int) -> None:
    """Terminate only the session/process group created for this one job."""

    validate_owned_group(process, pgid)
    if not group_exists(pgid):
        return
    os.killpg(pgid, signal.SIGTERM)
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    # If any member remains, this PGID still denotes the original group and
    # cannot have been reused. Kill the group as a unit; never enumerate PIDs.
    if group_exists(pgid):
        os.killpg(pgid, signal.SIGKILL)
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(f"isolated process group {pgid} survived SIGKILL") from error


def sample_group(pgid: int) -> tuple[float, int, str]:
    """Return aggregate CPU/RSS and the leader elapsed time for one PGID."""

    result = subprocess.run(
        ["ps", "-axo", "pid=,pgid=,%cpu=,rss=,etime="],
        check=False,
        capture_output=True,
        text=True,
    )
    total_cpu = 0.0
    total_rss = 0
    elapsed = "?"
    for line in result.stdout.splitlines():
        fields = line.split()
        if len(fields) < 5:
            continue
        try:
            pid = int(fields[0])
            row_pgid = int(fields[1])
            cpu = float(fields[2])
            rss = int(fields[3])
        except ValueError:
            continue
        if row_pgid != pgid:
            continue
        total_cpu += cpu
        total_rss += rss
        if pid == pgid:
            elapsed = fields[4]
    return total_cpu, total_rss, elapsed


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        usage="%(prog)s --name LABEL [--timeout SECONDS] [--input FILE] "
        "[--allow-duplicate] -- COMMAND [ARG ...]"
    )
    parser.add_argument("--name", required=True)
    parser.add_argument(
        "--timeout", type=int, default=int(os.environ.get("MAX11_CAS_TIMEOUT_SECONDS", "900"))
    )
    parser.add_argument("--input", type=Path)
    parser.add_argument("--allow-duplicate", action="store_true")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    arguments = parser.parse_args(argv)
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", arguments.name):
        parser.error("--name must contain only letters, digits, dot, underscore, or hyphen")
    if arguments.timeout <= 0:
        parser.error("--timeout must be positive")
    if arguments.command and arguments.command[0] == "--":
        arguments.command = arguments.command[1:]
    if not arguments.command:
        parser.error("a command is required after --")
    if arguments.input is not None:
        arguments.input = arguments.input.resolve(strict=True)
        if not arguments.input.is_file():
            parser.error(f"CAS input is not a file: {arguments.input}")
    return arguments


def finish(job_dir: Path, state: str, exit_code: int) -> None:
    atomic_text(job_dir / "exit_code", f"{exit_code}\n")
    atomic_text(job_dir / "ended_epoch", f"{int(time.time())}\n")
    atomic_text(job_dir / "state", f"{state}\n")


def fail_safety(job_dir: Path, output: IO[str], message: str) -> int:
    output.write(f"CAS_SAFETY_ERROR {message}\n")
    output.flush()
    finish(job_dir, "safety_error", EXIT_SAFETY)
    return EXIT_SAFETY


def main(argv: Sequence[str]) -> int:
    arguments = parse_args(argv)
    project_dir = Path(__file__).resolve().parent.parent
    state_root = project_dir / ".max11-lanes" / "cas"
    state_root.mkdir(parents=True, exist_ok=True)

    if not arguments.allow_duplicate:
        for prior_dir in state_root.iterdir():
            if not prior_dir.is_dir():
                continue
            try:
                same_name = (prior_dir / "name").read_text().splitlines()[0] == arguments.name
                running = (prior_dir / "state").read_text().splitlines()[0] == "running"
                prior_pid = int((prior_dir / "pid").read_text().splitlines()[0])
            except (FileNotFoundError, IndexError, ValueError):
                continue
            if same_name and running and pid_exists(prior_pid):
                print(
                    f"CAS_DUPLICATE name={arguments.name} active_job={prior_dir} pid={prior_pid}",
                    file=sys.stderr,
                )
                return EXIT_DUPLICATE

    stamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    job_dir = state_root / f"{stamp}-{arguments.name}-{os.getpid()}"
    job_dir.mkdir()
    started_epoch = int(time.time())
    atomic_text(job_dir / "name", f"{arguments.name}\n")
    atomic_text(job_dir / "started_epoch", f"{started_epoch}\n")
    atomic_text(job_dir / "timeout_seconds", f"{arguments.timeout}\n")
    atomic_text(job_dir / "state", "starting\n")
    atomic_text(job_dir / "command", f"{shlex.join(arguments.command)}\n")

    input_hash: str | None = None
    if arguments.input is not None:
        atomic_text(job_dir / "input", f"{arguments.input}\n")
        input_hash = sha256_file(arguments.input)
        atomic_text(job_dir / "input_sha256", f"{input_hash}\n")

    command_source: Path | None = None
    command_source_hash: str | None = None
    for argument in arguments.command:
        candidate = Path(argument)
        if candidate.is_file():
            command_source = candidate.resolve()
            command_source_hash = sha256_file(command_source)
            atomic_text(job_dir / "command_source", f"{command_source}\n")
            atomic_text(job_dir / "command_source_sha256", f"{command_source_hash}\n")
            break

    output_path = job_dir / "output.log"
    resources_path = job_dir / "resources.tsv"
    atomic_text(resources_path, "epoch\tpgid\tcpu_percent\trss_kib\telapsed\n")
    print(f"CAS_JOB={job_dir} TIMEOUT_SECONDS={arguments.timeout}", flush=True)

    input_stream: IO[bytes] | None = None
    try:
        if arguments.input is not None:
            input_stream = arguments.input.open("rb")
        with output_path.open("wb") as output:
            process = subprocess.Popen(
                arguments.command,
                stdin=input_stream,
                stdout=output,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            pgid = os.getpgid(process.pid)
            if pgid != process.pid or pgid <= 1:
                process.terminate()
                process.wait(timeout=5)
                with output_path.open("a") as text_output:
                    return fail_safety(
                        job_dir,
                        text_output,
                        f"new session validation failed: pid={process.pid} pgid={pgid}",
                    )
            atomic_text(job_dir / "pid", f"{process.pid}\n")
            atomic_text(job_dir / "pgid", f"{pgid}\n")
            atomic_text(job_dir / "state", "running\n")

            def interrupted(_signum: int, _frame: object) -> NoReturn:
                raise JobInterrupted

            previous_handlers = {
                watched: signal.signal(watched, interrupted)
                for watched in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
            }
            deadline = time.monotonic() + arguments.timeout
            try:
                while process.poll() is None:
                    cpu, rss, elapsed = sample_group(pgid)
                    with resources_path.open("a") as samples:
                        samples.write(
                            f"{int(time.time())}\t{pgid}\t{cpu:.1f}\t{rss}\t{elapsed}\n"
                        )
                    if time.monotonic() >= deadline:
                        try:
                            stop_owned_group(process, pgid)
                        except RuntimeError as error:
                            with output_path.open("a") as text_output:
                                return fail_safety(job_dir, text_output, str(error))
                        finish(job_dir, "timed_out", EXIT_TIMEOUT)
                        print(
                            f"CAS_EXIT={EXIT_TIMEOUT} STATE=timed_out LOG={output_path}",
                            flush=True,
                        )
                        return EXIT_TIMEOUT
                    time.sleep(min(2.0, max(0.0, deadline - time.monotonic())))
            except JobInterrupted:
                try:
                    stop_owned_group(process, pgid)
                except RuntimeError as error:
                    with output_path.open("a") as text_output:
                        return fail_safety(job_dir, text_output, str(error))
                finish(job_dir, "interrupted", EXIT_INTERRUPTED)
                return EXIT_INTERRUPTED
            except Exception as error:
                # A sampling or ledger failure must not strand an expensive
                # child. Cleanup still goes through the same fail-closed PGID
                # validation; no fallback ever walks or signals arbitrary PIDs.
                try:
                    stop_owned_group(process, pgid)
                    cleanup_note = ""
                except RuntimeError as cleanup_error:
                    cleanup_note = f"; cleanup refused: {cleanup_error}"
                with output_path.open("a") as text_output:
                    return fail_safety(
                        job_dir,
                        text_output,
                        f"supervisor failure: {error}{cleanup_note}",
                    )
            finally:
                for watched, previous in previous_handlers.items():
                    signal.signal(watched, previous)

            raw_exit = process.wait()
            exit_code = raw_exit if raw_exit >= 0 else 128 - raw_exit
    except (OSError, subprocess.SubprocessError) as error:
        with output_path.open("a") as text_output:
            text_output.write(f"CAS_START_ERROR {error}\n")
        finish(job_dir, "failed_to_start", EXIT_SAFETY)
        return EXIT_SAFETY
    finally:
        if input_stream is not None:
            input_stream.close()

    source_changed = False
    with output_path.open("a") as text_output:
        if arguments.input is not None and (
            not arguments.input.is_file() or sha256_file(arguments.input) != input_hash
        ):
            text_output.write(f"CAS_INPUT_CHANGED_DURING_RUN FILE={arguments.input}\n")
            source_changed = True
        if command_source is not None and (
            not command_source.is_file() or sha256_file(command_source) != command_source_hash
        ):
            text_output.write(f"CAS_SOURCE_CHANGED_DURING_RUN FILE={command_source}\n")
            source_changed = True

    if source_changed:
        exit_code = EXIT_SOURCE_CHANGED
        state = "source_changed"
    else:
        state = "succeeded" if exit_code == 0 else "failed"
    finish(job_dir, state, exit_code)
    print(f"CAS_EXIT={exit_code} STATE={state} LOG={output_path}", flush=True)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
