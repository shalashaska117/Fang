"""Route one fang invocation to exactly one installed profile.

Every input goes to the version-8 pipeline unless --profile explicitly selects
the restricted CNF or ground-FOF profile of an older installation. The choice
depends only on the command line, never on the input or on an earlier failure.
The router replaces itself with the selected command, so there is no retry and
no fallback between profiles.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import json
import os
from pathlib import Path
import sys

SCHEMA = "fang-command-v1"
PROFILES = ("v8", "cnf", "ground-fof")


def selected_profile(argv):
    """Return the profile and the arguments without the --profile option."""
    profile, rest, index = None, [], 0
    while index < len(argv):
        item = argv[index]
        if item == "--":
            rest.extend(argv[index:])
            break
        if item == "--profile" or item.startswith("--profile="):
            if profile is not None:
                raise ValueError("--profile may be given once")
            if item == "--profile":
                if index + 1 >= len(argv):
                    raise ValueError("--profile needs a value: " + ", ".join(PROFILES))
                profile, index = argv[index + 1], index + 2
            else:
                profile, index = item.split("=", 1)[1], index + 1
            if profile not in PROFILES:
                raise ValueError("unknown profile " + repr(profile) + "; choose one of: " + ", ".join(PROFILES))
            continue
        rest.append(item)
        index += 1
    return profile or "v8", rest


def load_command(path):
    value = json.loads(Path(path).read_text(encoding="utf-8"))
    profiles = value.get("profiles") if value.get("schema") == SCHEMA else None
    if (not isinstance(profiles, dict) or "v8" not in profiles or set(profiles) - set(PROFILES)
            or any(not isinstance(argv, list) or not argv or not all(isinstance(item, str) for item in argv)
                   for argv in profiles.values())):
        raise ValueError("Unsupported fang command configuration")
    return profiles


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    try:
        if len(argv) < 2 or argv[0] != "--command":
            raise ValueError("the installed launcher must supply --command")
        profiles, argv = load_command(argv[1]), argv[2:]
        if argv == ["help"]:
            argv = ["--help"]
        profile, rest = selected_profile(argv)
        if profile not in profiles:
            raise ValueError(f"profile {profile} is not installed here; no other profile was run")
    except (OSError, ValueError) as error:
        print("fang: " + str(error), file=sys.stderr)
        return 6
    command = profiles[profile] + rest
    os.execv(command[0], command)


if __name__ == "__main__":
    raise SystemExit(main())
