# Cross-repository source intake

Status: source inspection only. No Lean compiler was run. No archived proof-status sentence is adopted as a current compiler/axiom receipt.

The source branch `randogelist/snditeration` was read at commit `8e6f44efbde00d49c44859de6b382f71a7d5ab98`. The source branch `randogelist/BATCH-ONE` was read at commit/tree `387cdfd27efcedccc12780daaed7121a00148678`. Binary ZIP contents were retrieved with the GitHub plugin's base64 file API. Git blob hashes of all successfully retrieved archive bytes match GitHub's returned blob hashes.

## Selected active addition

Archive: `ZETAHYPERBOLIC_CHRONOLOGICAL_LEAN_v1_2_55_KREIN_SIGNATURE_PRINCIPAL_MINORS_FIX1.zip`.
Git blob: `4a3b0ba63d7843bacbef643d99798551cdfb2595`.
Archive SHA256: `7a9eb719dd3aeb69b7ed1fcfa6480f2e692de37de4492f4190ef635f88b1f0a4`.

`selected_src/` contains 19 new files, copied byte-for-byte. `selected_manifest.json` lists their full 50-module dependency closure: 31 modules are identical to canonical supplied package 20 and are not copied a second time. There are no missing local imports or same-path source conflicts in this selected closure. Mathlib dependencies are left to the recipient's compatible cache.

The useful final statements are:

| Declaration | Exact scope | Paper relation |
|---|---|---|
| `PaperAdvances.Corollary3_6.finite_hankel_gram` | Any finite real atoms and any truncation order; exact rectangular Vandermonde Gram factorization | Finite moment algebra |
| `PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_gram` | Same factorization with arbitrary real masses | Generalizes finite moment algebra |
| `...weighted_hankel_posSemidef` | Nonnegative masses; every order | Valid corrected part of Corollary 3.6 |
| `...weighted_hankel_det_zero_above_support` | Any masses; matrix order greater than number of indexed atoms | Obstruction to literal all-orders strict positivity |
| `PaperAdvances.Corollary3_6_ExactFiniteRank.weighted_posDef_up_to_support` | Distinct real atoms, positive masses, order n <= h | Sharp finite-support positivity |
| `...weighted_det_pos_iff_order_le_support` | Same assumptions; positive determinant iff n <= h | Exact finite-support criterion |
| `PaperAdvances.Corollary3_6_AllPrincipalMinors.weighted_all_principal_minors_nonnegative` | Nonnegative masses, every n, any principal-index map | Principal minors, including repeated indices |
| `...weighted_all_principal_minors_positive` | Distinct atoms, positive masses, n <= h, injective principal-index map | Strict principal-minor result, not arbitrary minors |

Some of the 19 dependency files are manuscript index wrappers or `#check` pointers. Their inclusion is required by the archive's imports and must not be counted as proof of the corresponding complete manuscript items. The final finite moment statements are generic algebraic facts; no identification with a particular original-pencil matrix is silently supplied.

## Necessary manuscript correction

The attached PDF's Corollary 3.6 forms a measure on finitely many atoms `u_j=(r_j-q0)^(-2)`. Hankel rank is bounded by the number of distinct atoms, so strictly positive Hankel determinants at all orders is impossible. Strict positivity through h requires injective atoms, which is stronger than distinct roots because opposite signed gaps can have the same square. The selected corrected statements must not be labeled manuscript-equivalent proof of the literal clause.

The same corollary's displayed finite factor inequality is reversed relative to its own proof. The valid inequality is `h^(-1/(2r)) <= S_(2r)^(-1/(2r))/d_min <= 1`; its displayed statement says `1 <= ratio <= h^(1/(2r))`. The selected files do not prove a limit theorem or silently correct this analytic endpoint. The remote file `ProofAdvances/Corollary_3_6_PowerSumExtrema.lean` contains a useful finite bound `U^r <= sum_i u_i^r <= h U^r`, retained for later integration.

## Other inspected archive candidates

- `ZETAHYPERBOLIC_PAPER_CHRONOLOGY_v0_6_0_9_CHRONOLOGICAL_PROOFS_3_2_TO_3_4.zip`, blob `cc536e6059043e39534994af112c4ded7cb0c4af`, SHA256 `df3a6c74df933302d58d78e1d18045556fa1b6c35ed10fa831adf9f6dfa2aa24`, 66 Lean files. Its new modules contain actual slope-congruence/left-right root classification and 3x3 Dodgson signs, with full signature counts, continuous total positivity and arbitrary-order interlacing explicitly open. Not selected because it imports a separate `PaperChronological` base and mostly overlaps selected algebraic coverage.
- `ZETAHYPERBOLIC_PRINCIPAL_THEOREMS_LEAN_v0_1_9_ZETA7_UNCONDITIONAL (2).zip`, blob `e96aca8cd872cfcc4c6ff4380164c2602fb789bb`, SHA256 `3588a70fdd6437624fea6df67ac567edf3ac4349e4f8013fc53c23cccfb7d5ac`, 154 Lean files. Contains a broader Section 5 candidate pool; the inspected dual positivity certificate interface explicitly assumes a weight-seven tail bound and finite positive/negative certificates. The archive filename alone is not evidence of any complete unconditional manuscript theorem. No Section 5 files selected in this increment.
- `ZETAHYPERBOLIC_PAPER_CHRONOLOGY_v0_6_4_0_CROSS_CHAPTER_FINITE_BRIDGES_433.zip`, blob `0d6a7bb8f92350a155ae630a68cde94b5e86b5eb`, metadata read only. Contents API returned empty data for this >1 MiB file; generic blob fetch also failed. It has not been inspected and is not integrated.

## Verification boundary

Local checks verified archive structure, Git blob SHA, selected module SHA256, dependency closure, and byte equality for overlapping source modules. These checks do not elaborate Lean or establish an axiom-clean proof. All selected additions await the user's native Lean 4.33.0 compiler and transitive axiom audit.
