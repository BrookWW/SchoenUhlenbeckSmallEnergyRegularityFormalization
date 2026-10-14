#!/usr/bin/env python3
"""Check public theorem axioms and scan the mathematical sources for proof gaps.

Run after `lake build`. The compiled dependency closures may use only propext,
Classical.choice, and Quot.sound. The source scan excludes comments and strings;
it covers project mathematics, not Mathlib or the inspection code in this script.
"""

import json
import re
import sys

from verification_common import (
    PROJECT, check_frozen_coverage, lean_output, load_theorems, parse_records,
    strip_comments_and_strings,
)


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# These exports are the reusable results displayed in the mathematical proof chain.
CHAIN_THEOREMS = {
    "Analysis.SobolevPoincare": ["MemW12.poincare_ball"],
    "Analysis.InnerVariationStationarity": ["IsLocallyEnergyMinimizing.innerVariation_stationarity"],
    "Analysis.RadialStressGeometry": ["weakRadialStressContractionFormula", "radialStressEnergyIdentity"],
    "Analysis.RadialStationarity": ["IsLocallyEnergyMinimizing.radial_stationarity"],
    "Analysis.RadiusBoundaryIdentity": ["IsLocallyEnergyMinimizing.radius_boundary_identity"],
    "Analysis.Monotonicity": ["IsLocallyEnergyMinimizing.monotonicity", "IsLocallyEnergyMinimizing.normalizedEnergy_monotoneOn"],
    "Analysis.CenteredEnergy": ["IsLocallyEnergyMinimizing.centered_energy_bound"],
    "Analysis.VariableShiftDiffeomorphism": ["variableShift_diffeomorphism"],
    "Analysis.VariableMollification": ["variableMollification_sobolev_estimates"],
    "Analysis.FixedSmoothing": ["fixedSmoothing_complete"],
    "Analysis.ProjectedCompetitor": ["projectedCompetitor_complete"],
    "Analysis.PoissonSourceDirichlet": ["poisson_source_closedData_dirichlet_assembly"],
    "Analysis.HarmonicReplacement": ["harmonicReplacement_fixedScale"],
    "Analysis.HarmonicReplacementEstimate": ["harmonicReplacement_projectedEnergy"],
    "Analysis.DecayGoodShell": ["decay_good_shell"],
    "Analysis.DecayCutoff": ["decay_cutoff_complete"],
    "Analysis.DecayComparison": ["decay_energy_comparison"],
    "Analysis.DecayThreshold": ["decay_threshold_complete"],
    "Analysis.AffineMinimizerTransport": ["affineBall_minimizer_transport"],
    "Analysis.EnergyIteration": ["energyIteration_complete"],
    "Analysis.CenteredEnergyGrowth": ["centeredEnergyGrowth_complete"],
    "Analysis.MorreyRepresentative": ["morrey_representative"],
    "Analysis.UnitBallRegularity": ["unitBallRegularity_complete"],
    "Analysis.GeneralBallRegularity": ["generalBallRegularity_complete"],
}

FORBIDDEN_TOKENS = {
    "sorry", "admit", "axiom", "sorryAx", "unsafe", "native_decide",
    "implemented_by", "extern", "ofReduceBool", "ofReduceNat", "trustCompiler",
    "skipKernelTC",
}


def scan_sources():
    paths = [PROJECT / "HarmonicMaps.lean"]
    paths += sorted((PROJECT / "HarmonicMaps").rglob("*.lean"))
    paths += [PROJECT / "HolderToCK.lean"]
    paths += sorted((PROJECT / "HolderToCK").rglob("*.lean"))
    if len(paths) < 2 or not paths[0].is_file():
        raise ValueError("Mathematical Lean sources are missing.")
    violations = []
    for path in paths:
        source = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for match in re.finditer(r"[A-Za-z_][A-Za-z0-9_']*", source):
            if match.group() in FORBIDDEN_TOKENS:
                line = source.count("\n", 0, match.start()) + 1
                violations.append(f"{path.relative_to(PROJECT)}:{line}: {match.group()}")
    if violations:
        raise ValueError("Forbidden proof-gap or trust-bypass token(s):\n" + "\n".join(violations))
    print(f"SOURCE CHECK PASS: {len(paths)} Lean files")


def main():
    records = load_theorems()
    check_frozen_coverage(records)
    scan_sources()
    modules = {record["module"] for record in records}
    names = {record["theorem"] for record in records}
    for module, exports in CHAIN_THEOREMS.items():
        modules.add("HarmonicMaps." + module)
        names.update("HarmonicMaps." + name for name in exports)
    names = sorted(names)
    code = "module\n" + "\n".join("public import " + module for module in sorted(modules))
    code += "\nmeta import Lean\nopen Lean\nrun_cmd do\n  let env ← getEnv\n  for n in ["
    code += ", ".join("``" + name for name in names)
    code += '''] do
    let some ci := env.find? n | throwError "missing theorem: {n}"
    let axioms ← Lean.collectAxioms n
    logInfo ("AXIOMJSON " ++ n.toString ++ " " ++ (toJson (axioms.toList.map Name.toString)).compress)
'''
    actual = parse_records(lean_output(code), "AXIOMJSON", names)
    for name in names:
        axioms = json.loads(actual[name])
        if not isinstance(axioms, list) or not all(isinstance(axiom, str) for axiom in axioms):
            raise ValueError(f"Malformed axiom list for {name}")
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"Disallowed axioms for {name}: {', '.join(sorted(unexpected))}")
        print("AXIOMS OK", name, ", ".join(sorted(axioms)) or "none")
    print(f"AXIOM CHECK PASS: {len(names)} theorem dependency closures")
    import check_upgrade_axioms
    check_upgrade_axioms.main()


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
