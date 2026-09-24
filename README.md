# Weak Wright's Conjecture

## Lean formalization via three unitary operators

A Lean 4 formalization of the main theorem and consequences in *Phase retrieval with three unitary operators* by Lukas Liehr, Daniel Omer, and Mitchell A. Taylor (manuscript dated September 17, 2026).

The main result constructs one orthogonal projection on complex-valued `L²(ℝ)` such that `I + (ηⱼ − 1)P` gives phase retrieval for every three distinct unimodular scalars. The library also proves the order-three and near-identity corollaries, spatial transfer to standard Borel measure spaces and their completions, and nonuniform stability for the same projection.

```lean
import OperatorPhaseRetrieval

#check OperatorPhaseRetrieval.main
#check OperatorPhaseRetrieval.main_with_instability
```

## Build and verify

Install [Elan](https://github.com/leanprover/elan), then run these commands from the repository root:

```sh
lake exe cache get
lake build --wfail
lake env lean -DwarningAsError=true Audit.lean
```

The first command obtains precompiled Mathlib dependencies. A fresh checkout needs network access for the pinned toolchain and dependencies. No paper-specific dependencies outside this repository are required.

Versions are pinned:

- Lean `v4.33.0`
- Mathlib `v4.33.0`, commit `db584cd6d46c92f209a44c0f1c829460d327499d`
- Transitive dependencies are recorded in `lake-manifest.json`.

`Audit.lean` checks every declaration in the `OperatorPhaseRetrieval` namespace. It fails if a declaration depends on any axiom other than `propext`, `Classical.choice`, or `Quot.sound`, including any dependence on `sorryAx`.

## Repository layout

```text
OperatorPhaseRetrieval.lean           Complete library import
OperatorPhaseRetrieval/               34 proof modules and shared Mathlib imports
  Main.lean                          Theorem 2.1 and its first corollaries
  Consequences.lean                  Corollaries on general spaces
  TransferredInstability.lean         Theorem 2.1 and instability for one projection
  ...                                Analytic, operator, and measure-theoretic proofs
Audit.lean                           Axiom allowlist check
standalone/                          Generated Mathlib-only single-file version
scripts/make_standalone.py            Reproducible standalone generator
.github/workflows/lean.yml            Build, audit, and synchronization checks
docs/COVERAGE.md                      Paper-to-code map and construction details
docs/VERIFICATION.md                  Local verification record
```

Import `OperatorPhaseRetrieval` for all results, or a particular module for a narrower dependency set. All theorem names remain in the `OperatorPhaseRetrieval` namespace. The main theorem requires no additional analytic-model or spatial-isomorphism hypotheses.

## Single-file version

The standalone file includes the same definitions and proofs and imports only Mathlib. It can be used in a Mathlib project with the pinned versions. It is checked separately from the modular library to avoid duplicate declarations.

```sh
python3 scripts/make_standalone.py
python3 scripts/make_standalone.py --check
lake env lean -DwarningAsError=true standalone/Operator_Phase_Retrieval_Standalone.lean
```

Edit the modular sources, then regenerate the standalone file. The generator fails if the library root omits a source module, if imports form a cycle, or if a non-Mathlib external import is introduced.

## Relation to the paper

See [the coverage map](docs/COVERAGE.md) for theorem names and precise scope. The polynomial approximation argument proves the special case needed for the construction, rather than the full Mergelyan theorem. The smoothing weights are an alternative choice satisfying the required bounds. These choices preserve the main theorem and corollaries.

The manuscript PDF is not bundled in this repository. The authors of the associated paper are listed above; software authorship and licensing metadata can be supplied by the repository owner.

## Continuous verification

The GitHub workflow builds the library with warnings treated as failures, runs the axiom audit, and checks that the standalone file is current and accepted by Lean. It follows the documented [Lean action](https://github.com/leanprover/lean-action) and [checkout action](https://github.com/actions/checkout) interfaces. Local results and the scope of testing are recorded in [VERIFICATION.md](docs/VERIFICATION.md).

## License

No distribution license has been selected in this prepared source tree.
