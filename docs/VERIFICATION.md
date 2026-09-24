# Verification record

Verified locally on September 24, 2026, on macOS ARM64.

- Lean: `4.33.0`, commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- Mathlib: `v4.33.0`, commit `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Proof modules: 34, plus shared Mathlib imports and the library root.
- Named source declarations: 332, including 272 theorems; names and theorem bodies are preserved from the corrected standalone input.

| Check | Result |
|---|---|
| Lake build with `--wfail` | Passed; exit code 0; no warnings or errors |
| `Audit.lean` with `warningAsError=true` | Passed; 509 project declarations checked |
| Allowed axiom set | `propext`, `Classical.choice`, `Quot.sound` only |
| Generated standalone synchronization | Passed |
| Generated standalone with `warningAsError=true` | Passed; exit code 0; no output, warnings, or errors |
| Preservation of all 34 original proof bodies | Passed |

The axiom count includes generated helper declarations, so it is larger than the count of named source declarations. Splitting a source file changes sharing of these generated helpers, without adding mathematical assumptions.

The local build reused the installed pinned dependency checkouts and compiled Mathlib cache through Lake package path overrides. ProofWidgets was copied into a writable scratch directory for its build metadata. These machine-local overrides and dependency copies are not included in the repository; `lakefile.toml` and `lake-manifest.json` use portable GitHub revisions.

The [first GitHub Actions run](https://github.com/danielomer0802-sudo/weak-wrights-conjecture/actions/runs/36008990921) passed on September 24, 2026, for commit `e2edec432ff26b5fa3b89abf00369ff18f3a776e`. On the `ubuntu-latest` runner, it successfully built the modular library, audited the project declarations, checked standalone synchronization, and checked the standalone formalization. This also verified fresh dependency downloads and the portable dependency configuration. The supplied PDF has not been edited or bundled.

See [verification.log](verification.log) for the successful build and axiom-audit output. Reproduce the checks with the commands in the [README](../README.md).
