# Leaned Paper — YOU_ARE_GOODWORKFLOWFRONTIER

The [`leaned-paper`](https://github.com/randogelist/zetahyperbolic-axiom/tree/leaned-paper) branch builds a manuscript-aligned Lean formalization from the supplied project archives, commit-pinned cross-branch Lean bases and documented research inputs. This increment is `v0_1_2_construction`, with 96 active modules in `modules.txt`.

**Local Linux validation passed: 96/96 modules and the independent transitive axiom audit. Native Windows validation remains pending. The complete paper and its quantitative irrationality endpoints are not proved by this increment.**

On 2026-10-25 the user explicitly authorized local Lean installation and compilation. Local validation uses Lean 4.33.0 and commit-pinned Mathlib; its compiler logs, source/environment fingerprints and axiom receipt are recorded separately under `validation/linux/`. The current local status is `LINUX_LEAN433_PASS_AXIOM_AUDITED`; see [acceptance](validation/linux/acceptance.json) and [compiler summary](validation/linux/summary.json). A successful Linux run does not certify the Windows CMD runner or permit reuse of Linux `.olean` files as native Windows artifacts.

## Exchange with the from-scratch rebuild

The [comparison with snditeration](docs/SNDITERATION_EXCHANGE.md) selects its three direct partial-fraction modules and connects them to the actual kernel and Gram integral. The imported declarations retain their proof bodies; only import paths change. The new algebraic identity holds for every real square argument and arbitrary parameter data. The Gram integral theorem requires only a positive odd-weight index. All 91 previous mathematical/auditor-helper sources remain byte-identical; the final audit is extended. The stronger assembled Gram, singular-slope, principal-minor and arithmetic transfer results are retained.

## Preserved previous increment

Five mathematical modules extend the selected paper core and cross-branch sources:

| Source | Exact contribution | Remaining boundary |
| --- | --- | --- |
| `LeanPaper/PullbackReflection.lean` | Function-level square-pole substitution with the entire polynomial quotient; its canonical normal-form moment equality; finite-span reflection and finite-pole difference. | Arbitrary `RatFunc` representation independence and full polynomial-plus-pole difference assembly remain open. |
| `LeanPaper/SingularSlope.lean` | Constructs spectral factors for a symmetric affine pencil with positive definite base, allowing zero slope eigenvalues. Every existing complex determinant zero is real. | No nonsingularity, fixed root count or interlacing is inferred for a restricted slope. |
| `LeanPaper/PrincipalMinorRealRoots.lean` | Identifies each actual rational principal determinant with its real affine pencil, derives its positive base from the original analytic Gram construction, and proves all its complex zeros real. | Exact degree/rank and rank-sensitive interlacing remain separate. |
| `LeanPaper/SingularPrincipalMinorExample.lean` | Computes the actual residue formula at `k=2,m=1,N=1,K=6`, obtains zero first slope, and derives a positive constant leading minor with no roots. | This corrects the printed universal root-enumeration clause of Theorem 3.4; it does not refute eigenvalue interlacing or Dodgson condensation. |
| `LeanPaper/ReciprocalRootMoments.lean` | Constructs the actual determinant root vector and coalesces equal inverse-square gaps into distinct atoms with positive multiplicities. At a rational non-root shift, ordinary and shifted Hankel matrices are PSD at every order; strict determinant positivity holds exactly through distinct support size. | Log-derivative identification, rationality and the nearest-root limit/rate remain open. |

The preserved principal-minor center result establishes positive evaluation at the true odd-zeta center. The corrected reciprocal-root result no longer assumes that distinct roots have distinct squared gaps. Opposite gaps are explicitly allowed to coalesce. No finite Gram statement supplies the missing arithmetic growth estimates.

## Evidence and manuscript scope

The [45-item ledger](docs/manuscript_45_ledger.csv) separates source scope, local compiler status and native Windows status. Its [JSON version](docs/manuscript_45_ledger.json) retains the same items and open obligations. Compilation and an axiom audit certify the exact Lean statements; semantic equivalence to each complete printed theorem is an additional obligation.

[Manuscript issues](docs/manuscript_issues.txt) preserve the literal claims and corrections separately. Theorem 3.4 can have a constant first principal minor. Corollary 3.6 cannot have strictly positive finite-support Hankel determinants at every order, and its displayed factor bound and odd log-derivative sign require correction. Historical numerical target variants are not silently substituted for the uploaded paper's constants.

The exhaustive project audit checks transitive axioms for declarations owned by the active modules and permits only `propext`, `Quot.sound` and `Classical.choice`. It rejects `sorryAx`, custom axioms and native-decide assumptions. `LeanPaper/AxiomWalk.lean` provides the audit traversal and `LeanPaper/KernelAudit.lean` applies the gate. An audit pass does not discharge explicit mathematical hypotheses or certify still-open ledger rows.

## Native Windows run and cache reuse

Extract the ZIP and call its sole `run.cmd` from Windows CMD. Use installed native Lean 4.33.0 and compatible cached Mathlib. The runner is offline and does not run Lake setup, Python, PowerShell or WSL. [Native runner documentation](docs/NATIVE_RUNNER.md) describes cache paths, provenance checks and receipts.

Only previously passed native objects with matching source, object, import, toolchain, Mathlib, flags and environment fingerprints are reusable. New or invalidated modules are compiled, and any source, dependency or final audit failure stops acceptance. The local Linux receipt is separate evidence and cannot stand in for these native cache checks.

## Next execution targets

1. Obtain a separate native Windows receipt; preserve the compatible local and native passed artifacts under their separate fingerprints.
2. Close representation independence and the remaining full-domain identities for Lemmas 2.2–2.3.
3. Prove the principal degree/rank law and corrected interlacing; separately address mixed-minor total positivity and signature counts.
4. Connect reciprocal-root moments to the corrected log-derivative formula, rationality and nearest-root limit.
5. Assemble real-parameter, character and arithmetic growth inputs in manuscript order, keeping every quantitative endpoint explicit.

`provenance/` records attachment hashes, source choices, collisions, pinned repository origins, research inputs and the local environment. See [cross-repository source intake](docs/REMOTE_BASE_AUDIT.md) for the earlier selection and its scope. Archived status prose is historical evidence only. The exact names `YOU_ARE_GOODWORKFLOWFRONTIER`, `LEAN_ANCHORINGS` and all seven `ZETA_HYPERBOLIC_ANCHOR` identifiers are preserved.
