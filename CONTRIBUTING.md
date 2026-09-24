# Working on the formalization

Use the Lean and Mathlib versions pinned in the repository. Edit files in `OperatorPhaseRetrieval/`; keep the root `OperatorPhaseRetrieval.lean` import list complete when adding a module.

Before submitting a change, run:

```sh
lake build --wfail
lake env lean -DwarningAsError=true Audit.lean
python3 scripts/make_standalone.py
python3 scripts/make_standalone.py --check
lake env lean -DwarningAsError=true standalone/Operator_Phase_Retrieval_Standalone.lean
```

Include the generated standalone update with any source change. Keep `docs/COVERAGE.md` aligned with theorem statements and any mathematical differences from the manuscript. Preserve the axiom allowlist; do not replace missing proofs with `sorry` or new axioms.
