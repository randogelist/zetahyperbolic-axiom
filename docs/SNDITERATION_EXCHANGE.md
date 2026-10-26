# Exchange with the from-scratch rebuild

The useful exchange is the direct partial-fraction construction. The rebuilt
foundation, analytic and spectral modules largely split the same declarations
already compiled here. They do not replace the stronger assembled endpoints.

The comparison pins `randogelist/snditeration` main at
`97802e189e668e4d3b36707497ed0b25255f6400` and the explicit-pole-residues branch at
`ec90bd0be7c3889b71be719ec1404dae385b27a6`. Both use Lean 4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. All twelve visible branches were
inspected. Main contains all mathematical sources in the other branches except
the newer `PartialFractionsResidues.lean`; umbrella/audit files also differ.
The upstream README and ledger lag the actual main tree, so the comparison
uses the pinned source statements rather than those progress labels.

| Rebuild input | Decision | Reason and existing counterpart |
| --- | --- | --- |
| Section2/Moments, BasisInvariance, PoleDiagonalization | Retain current implementations | All 80 declarations have identical normalized statement/proof bodies in Definition_2_1 and Theorems_2_4/2_5. The same fully qualified names already exist. |
| Affine pencil, Hermitian factorization, root and gap modules | Retain current implementations | The same proofs are in Theorem_3_1_Universal_Hyperbolicity and General_Odd_Weight_Endpoint. Together with the two moment-realization modules, all 83 declarations match. |
| Density, moments, Bose tails, coth, scaling and pole integral | Retain current implementations | The corresponding Theorem_3_1 modules already supply these inputs. Analytic review found 78 exact normalized matches and two visibility/inferred-binder variants; this count overlaps the moment modules above. |
| Section4/Transfer | Retain current, stronger module | Its 10 declarations match a subset of our 21. Replacing the file would discard the spectral-to-local-comparison construction and arithmetic helper results. |
| PartialFractionsCore and PartialFractionsQuotient | Import with local paths | Constructs the decomposition directly over Real.Parameters, identifying its quotient with the actual Euclidean quotient. Existing analogous sources use HankelParams and a translation layer. |
| Feature branch PartialFractionsResidues | Import with local paths | Proves residues equal the actual derivative formula and assembles the exact polynomial-plus-poles identity. |

The three imported files live under `src/LeanPaper/Rebuild/`. Only their import
paths change; every declaration and proof body is preserved. Exact origin
commits, upstream blob hashes, source hashes and active hashes are recorded in
`provenance/snditeration_exchange.json`. Importing the duplicated rebuild
foundation beside the current definitions would cause duplicate declarations.
Future modules can instead redirect those imports to their existing owners.

`LeanPaper.RebuildKernelBridge` makes the exchange usable by the manuscript:

1. `tailD_eval_square_pos` proves the denominator positive at every real square,
   for arbitrary `Real.Parameters`, including empty tail products.
2. `resolvedKernel_eq_fraction_all_real` identifies the existing kernel with the
   numerator divided by the tail denominator for every real argument. It needs
   neither admissibility nor a positive argument; zero is included.
3. `gram_eq_fraction_integral` combines that identity with the already proved
   pole integral theorem. For `0 < p.k`, each actual Gram entry at zeta equals
   the rational-kernel integral. No additional m/N/K restrictions are assumed.

The older positive-argument theorem and all previously passed mathematical
sources are retained unchanged. This supplies an alternate direct algebraic
input and a broader identity; it does not replace the existing dependency path
of `MAIN_CHAIN_ASSEMBLED`. That assembly already constructs the weighted
measure and discharges Gram positivity under its required hypotheses.

Keep the singular-slope theorem, actual principal-minor results, counterexample
and corrected reciprocal-root moments. The incoming sources do not subsume
them. Neither repository closes arbitrary RatFunc representation independence,
the full rational-function reflection/difference domain, mixed-minor positivity,
corrected interlacing, the quantitative asymptotic index budget, or unconditional
zeta irrationality. This exchange does not change those ledger boundaries.

Compilation and the independent transitive axiom audit are recorded separately
in `validation/linux/acceptance.json`. Native Windows validation remains pending.
