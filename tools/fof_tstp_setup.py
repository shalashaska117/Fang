"""Required proof inventory for the ground-FOF source build."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import json

TEXT_THEOREM = "Fang.FofTstpExport.RenderProof.decoded_render_checked_text"
TEXT_MODULE = "Fang.FOF.TSTP.Audit"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def read_inventory(frozen):
    value = json.loads((frozen / "tools/fof_proof_inventory.json").read_text())
    if (set(value) != {"schema", "modules", "audits"}
            or value["schema"] != "fang-ground-fof-proof-inventory-v1"
            or len(value["modules"]) != len(set(value["modules"]))
            or not set(value["audits"]) <= set(value["modules"])
            or any(len(names) != len(set(names)) for names in value["audits"].values())
            or TEXT_THEOREM not in value["audits"].get(TEXT_MODULE, [])):
        raise ValueError("Required ground-FOF proof inventory differs")
    return value


def check_proofs(frozen, proof):
    expected = read_inventory(frozen)
    wanted = {(module, name) for module, names in expected["audits"].items() for name in names}
    actual = [(row["module"], row["declaration"]) for row in proof["axiom_audits"]]
    if (proof["status"] != "passed"
            or sorted(proof["completed_modules"]) != sorted(expected["modules"])
            or len(actual) != len(wanted) or set(actual) != wanted
            or proof["declared_axiom_audits"] != len(wanted)):
        raise ValueError("Required combined proof inventory did not pass or an audit differs")
    if any(not set(row["axioms"]) <= ALLOWED_AXIOMS for row in proof["axiom_audits"]):
        raise ValueError("Unexpected FOF theorem axiom")
    return expected
