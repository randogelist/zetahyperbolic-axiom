# Independent semantic audit: original Proposition 4.2

## Verdict

The source endpoint `ManuscriptChain.Section4AlgebraicHeight.proposition_4_2_algebraic_numbers` covers the complete original Proposition 4.2 on manuscript page 15. Promotion to verified remains conditional on successful compilation and the transitive axiom audit for the exact receiving source SHA. This review performed no Lean or Lake execution.

This is an exact conditional transfer theorem. Its hypotheses are those of the printed criterion; it does not discharge the separate concrete zeta-family hypotheses in 4.4–4.8 or assert unconditional odd-zeta irrationality.

## Clause-by-clause comparison

| Printed clause | Source realization | Assessment |
| --- | --- | --- |
| Real center ξ; positive lattice spacing d₀; integer-polynomial sequence on positive multiples of d₀ | `ξ : ℝ`, `Q : ℕ → ℤ[X]`, `d0 : ℕ`, `hd0 : 0 < d0`; every growth/root hypothesis evaluates `Q (d0*n)` eventually as `n → ∞` | Exact positive-lattice content. The value at zero and values outside the lattice are irrelevant to the eventual hypotheses. |
| λ, ε, ρ > 0 and degree bound deg Q_K ≤ λK for all sufficiently large K | `hlam`, `hρ`, eventual `hdegree`; ε positivity follows from `hgap` and the proved nonnegativity of the upper height rate | No stronger omitted hypothesis. Allowing eventual degree bounds is at least as general as the printed setup. |
| 0 < abs Q_K(ξ) ≤ exp(−εK²) | `hvalues`, using actual `RealTransfer.evalReal` of integer polynomials | Exact. Nonzero polynomial/evaluation facts are derived rather than separately assumed. |
| Every complex root has distance at least exp(−ρK) from ξ | `hroots` over the roots multiset of the actual complex-coefficient image of `Q (d0*n)` | Exact all-root condition, preserving multiplicity. No real-root or pencil hypothesis is added. |
| limsup K⁻² log H(Q_K) ≤ Λ_height | `hheight` in `EReal`, with the same normalization `(d0*n)²` and actual coefficient height | Correct finite-upper-limsup formulation, avoiding an undefined/default unbounded real supremum convention. |
| d ≥ 1 and ε > (d−1)Λ_height | `hd : 1 ≤ d` and `hgap` | Exact. Natural subtraction agrees with integer subtraction under `hd`. |
| Every μ > λρd/(ε−(d−1)Λ_height) | `hμ` with the identical expression | Exact printed exponent, even though a lower helper proves a stronger sufficient exponent before this wrapper. |
| There exists a uniform height threshold B₀(μ) | `∃ B₀ : ℕ` outside all approximant quantifiers | Exact existential threshold; the paper does not demand an effective threshold in 4.2. |
| Every algebraic α of degree [ℚ(α):ℚ] ≤ d | `∀ α : ℂ`, `IsAlgebraic ℚ α`, `Module.finrank ℚ (IntermediateField.adjoin ℚ {α}) ≤ d` | Actual algebraic numbers and actual extension degree, not abstract polynomial/root proof fields. |
| Naive height H(α) and distance bound H(α)^−μ < abs(ξ−α) | `algebraicHeight α`, defined from a constructed primitive integer minimal polynomial; strict bound against the complex norm | Exact notion of naive algebraic height and strict conclusion. |

## Construction checks

`integerMinimalPolynomial` clears denominators of `minpoly ℚ α` through `IsLocalization.integerNormalization` and removes integer content with `primPart`. `integerMinimalPolynomial_spec` proves primitivity, rational irreducibility, the actual root equation and equality of degree with the rational minimal polynomial. `integerMinimalPolynomial_degree` identifies that degree with the extension degree. The sign choice of a primitive minimal polynomial does not affect naive coefficient height.

`Section4Resultant.naiveHeight` is the complex coefficient supremum norm of the integer polynomial, i.e. the maximum absolute integer coefficient. `Section4ConjugateBounds.naiveHeight_is_nat` constructs its natural value; `one_le_naiveHeight` provides the necessary lower bound for nonzero integer polynomials.

The proof chain constructs the actual Sylvester resultant and its conjugate-product identity; proves the nonzero integer lower bound through irreducibility and a proved nonzero evaluation; establishes coefficient/Mahler upper bounds; obtains uniform asymptotic budgets and index selection; converts the finite limsup to eventual exponential height bounds; and finally transfers to the actual primitive minimal polynomial of each α. No hypothesis simply asserts the needed resultant identity, height conclusion or approximation conclusion.

## Sources inspected

- Original PDF page 15 (accessible extraction `section4-manuscript.txt`).
- `src/LeanPaper/Section4AlgebraicHeight.lean`.
- `src/LeanPaper/Section4AlgebraicLattice.lean`.
- `src/LeanPaper/Section4AlgebraicLimsup.lean`.
- `src/LeanPaper/Section4AlgebraicTransfer.lean`.
- `src/LeanPaper/Section4Resultant.lean`.
- `src/LeanPaper/Section4ConjugateBounds.lean`.
- Declaration and proof-route inventory in `Section4AlgebraicBudget.lean` and `Section4ComplexComparison.lean`.

No semantic weakening or additional open premise was found. Older continuation-review prose saying that the exponent/index/minimal-height assembly remains missing is superseded by these actual source endpoints, but successful receiving compilation and audit must still be recorded separately.
