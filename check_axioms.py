"""Require a kernel axiom report for every advertised formal result."""
import re
import sys
from pathlib import Path

allowed = {"propext", "Classical.choice", "Quot.sound"}
required = {
    "UpperLayers.missing_rank_bound",
    "UpperLayers.exact_averaging_criterion",
    "UpperLayers.finite_criterion",
    "UpperLayers.hundred_element_cutoff",
    "UpperLayers.cutoff_59",
    "UpperLayers.cutoff_60",
}
reports = {}
output = Path(sys.argv[1]).read_text()
for name, dependencies in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
    reports[name] = {a.strip() for a in dependencies.split(",") if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
    reports[name] = set()
if missing := required - reports.keys():
    raise SystemExit(f"Missing axiom reports: {sorted(missing)}")
for name, dependencies in sorted(reports.items()):
    if unexpected := dependencies - allowed:
        raise SystemExit(f"{name} depends on unexpected axioms: {sorted(unexpected)}")
print(f"Audited {len(reports)} theorem reports, including all {len(required)} required results.")
