"""Install the public command over an explicitly selected checked pipeline."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shlex
import sys

from fang_szs.supervisor import write_json


def provision(output, *, fof=False, python=None):
    """Create a new launcher. Never replace an existing command or raw engine."""
    output = Path(output).resolve()
    source = output / "source/tools"
    config = output / ("fof-capability.json" if fof else "installation.json")
    if not config.is_file():
        raise ValueError("The checked pipeline must be installed before its public command")
    package = source / "fof_szs" if fof else source
    module = "main" if fof else "fang_szs.app"
    bootstrap = ("import sys; sys.dont_write_bytecode = True; "
                 "sys.path.insert(0, sys.argv.pop(1)); "
                 f"from {module} import main; raise SystemExit(main(public=True))")
    command = [str(python or Path(sys.executable).resolve()), "-B", "-c", bootstrap,
               str(package), "--capability" if fof else "--installation", str(config)]
    launcher = output / "bin/fang"
    with launcher.open("x", encoding="utf-8") as stream:
        stream.write('#!/bin/sh\nif [ "$#" -eq 1 ] && [ "$1" = "help" ]; then\n'
                     '  set -- --help\nfi\nexec ' + shlex.join(command) + ' "$@"\n')
    launcher.chmod(0o755)
    write_json(output / "command-receipt.json", {
        "status": "installed", "finished_utc": datetime.now(timezone.utc).isoformat(),
        "command": str(launcher), "command_sha256": hashlib.sha256(launcher.read_bytes()).hexdigest(),
        "pipeline": "cnf-and-ground-fof" if fof else "cnf", "configuration": str(config),
        "configuration_sha256": hashlib.sha256(config.read_bytes()).hexdigest(),
        "scope": "Public launcher only. Logical results use the selected installed checking pipeline.",
    })
    return launcher


def public_command(python, package, module, option, config):
    """The command line of one public adapter, run from its own installed sources."""
    bootstrap = ("import sys; sys.dont_write_bytecode = True; "
                 "sys.path.insert(0, sys.argv.pop(1)); "
                 f"from {module} import main; raise SystemExit(main(public=True))")
    return [str(python), "-B", "-c", bootstrap, str(package), option, str(config)]


def provision_v8(output, *, older=None, python=None):
    """Create the fang command over the v8 capability; older profiles only by explicit --profile.

    `older` names an earlier CNF and ground-FOF installation. Its profiles run
    from that installation's own pinned sources and configuration files. Never
    replace an existing command.
    """
    output = Path(output).resolve()
    tools = output / "source/tools"
    python = Path(python or sys.executable).resolve()
    if not (output / "v8-capability.json").is_file():
        raise ValueError("The v8 capability must be installed before its public command")
    profiles = {"v8": public_command(python, tools / "v8_szs", "main", "--capability", output / "v8-capability.json")}
    if older is not None:
        older = Path(older).resolve()
        for name, config, package, module, option in (
                ("cnf", "installation.json", "source/tools", "fang_szs.app", "--installation"),
                ("ground-fof", "fof-capability.json", "source/tools/fof_szs", "main", "--capability")):
            if not (older / config).is_file() or not (older / package).is_dir():
                raise ValueError("Older installation lacks the " + name + " profile")
            profiles[name] = public_command(python, older / package, module, option, older / config)
    command_path = output / "command.json"
    command = {"schema": "fang-command-v1", "profiles": profiles,
               "routing": "v8 unless --profile selects another installed profile; no retry or fallback"}
    with command_path.open("x", encoding="utf-8") as stream:
        json.dump(command, stream, indent=2, sort_keys=True)
        stream.write("\n")
    bootstrap = ("import sys; sys.dont_write_bytecode = True; "
                 "sys.path.insert(0, sys.argv.pop(1)); "
                 "from fang_router import main; raise SystemExit(main(sys.argv[1:]))")
    launcher = output / "bin/fang"
    with launcher.open("x", encoding="utf-8") as stream:
        stream.write("#!/bin/sh\nexec " + shlex.join([str(python), "-B", "-c",
                     bootstrap, str(tools), "--command", str(command_path)]) + ' "$@"\n')
    launcher.chmod(0o755)
    write_json(output / "command-receipt.json", {
        "status": "installed", "finished_utc": datetime.now(timezone.utc).isoformat(),
        "command": str(launcher), "command_sha256": hashlib.sha256(launcher.read_bytes()).hexdigest(),
        "pipeline": "v8", "configuration": str(command_path),
        "configuration_sha256": hashlib.sha256(command_path.read_bytes()).hexdigest(),
        "profiles": sorted(command["profiles"]),
        "scope": "Public launcher only. Each invocation runs exactly one profile, chosen by --profile (default v8).",
    })
    return launcher
