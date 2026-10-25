# Formalization status — YOU_ARE_GOODWORKFLOWFRONTIER

**Global validation: LINUX_LEAN433_PASS_AXIOM_AUDITED.** All 166 modules, including the 12-module increment, passed the expanded runner and independent transitive axiom audit. Sources are frozen. Native Windows has not run. The complete manuscript is not certified.

**Whole printed statements covered: 2 of 45 — Theorem 3.1 and Proposition 4.3.** The former now includes the literal Euclidean operator-norm disk for the actual primitive integer polynomial. The latter has exactly the printed p-adic nonvanishing and disk-membership hypotheses. Other items have precise components or outstanding obligations below.

| Classification | Items |
| --- | ---: |
| Verified | 1 |
| Already proved and retained | 1 |
| Partially formalized | 24 |
| In progress | 0 |
| Blocked | 3 |
| Not formalized | 16 |

“Verified” denotes a complete printed result closed by the current increment; “Already proved and retained” denotes complete baseline coverage. “Partially formalized” includes genuine exact components and explicitly identified conditional helpers. “Blocked” preserves a literal statement/formula obstruction, while corrected variants can be proved. “Not formalized” means no active manuscript-equivalent component was mapped; it is not a claim that the theorem is false. No source target remains labeled in progress in this completed snapshot; compiler and axiom evidence remain distinct from semantic coverage.

The current receipt counts 2,248 project declarations and 1,710 kernel theorem declarations, including generated/private declarations. These are not counts of proved manuscript theorems. All project dependencies passed the independent transitive audit with only `propext`, `Quot.sound`, and `Classical.choice`. A wrapper, `#check`, target definition or assumed conclusion receives no full-item credit.

## Definition 2.1 and main constructions (outside the 45-result count)

The manuscript contains one numbered Definition (2.1). Main surrounding constructions are mapped separately below. Additional modified-family constructions are recorded with their numbered theorem rows; listing a definition does not certify its analytic/arithmetic claims.

| Definition / construction | Status and exact boundary |
| --- | --- |
| Definition 2.1 — Order-s rational moment functional | **Partially formalized.** The printed Bernoulli monomial moments and harmonic simple-pole moments are defined over Q; arbitrary polynomial plus finite simple-pole normal forms have an explicit polynomial-valued mu. Representation uniqueness and the exact algebraic rational-function domain are new compiled and independently axiom-audited constructions. **Remaining:** Lift mu and tau as linear maps on their RatFunc subspaces and assemble their substitution identities. Defined moment values do not themselves prove linear-functional domain identification or analytic realization. Sources: [`ManuscriptChain.Real.monomialMoment`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.polynomialMoment`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.poleConstant`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`Zetahyperbolic.RatMomentElem`](../src/Zetahyperbolic/Section2Checked.lean); [`Zetahyperbolic.muFunctionalPoly`](../src/Zetahyperbolic/Section2Checked.lean); [`LeanPaper.Section2RepresentationIndependence.muOnDomain`](../src/LeanPaper/Section2RepresentationIndependence.lean); [`LeanPaper.Section2RationalDomains.muDomain_iff_denom_dvd`](../src/LeanPaper/Section2RationalDomains.lean) |
| parameters — Parameters, denominators and quotient/residue data | **Constructed and retained.** Actual k,m,N,K, weight 2k+1, h=K-N, admissibility, D_N, tail denominator, polynomial quotient and residues are explicit. **Remaining:** No extra arithmetic/asymptotic theorem follows from these definitions. Sources: [`ManuscriptChain.Real.Parameters`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.Admissible`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.D`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.tailD`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.quotient`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.residue`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean) |
| zeta_center — Harmonic sums and true zeta center | **Constructed and retained.** The rational harmonic sums and convergent positive real zeta series are defined; the series is identified with the real part of Mathlib riemannZeta. **Remaining:** The identification supplies no irrationality statement. Sources: [`ManuscriptChain.Real.harmonic`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.zeta`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.zeta_eq_riemannZeta_re`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean) |
| tau — Tau functional and its simple integer-pole domain | **Partially formalized.** Bernoulli tau monomial/pole generators and finite-span tau are explicit; the new TauDomain is exactly the rational functions whose denominator divides a finite product of distinct integer linear factors. **Remaining:** Lifted RatFunc linearity and actual substitution/reflection maps remain open; finite moment identities and representation independence are separate verified components under the current audit. Sources: [`Zetahyperbolic.tauMonomial`](../src/Zetahyperbolic/Section2Checked.lean); [`Zetahyperbolic.tauPolePoly`](../src/Zetahyperbolic/Section2Checked.lean); [`LeanPaper.PullbackReflection.tauFiniteSpan`](../src/LeanPaper/PullbackReflection.lean); [`LeanPaper.Section2TauRepresentation.TauDomain`](../src/LeanPaper/Section2TauRepresentation.lean); [`LeanPaper.Section2TauRepresentation.tauOnDomain`](../src/LeanPaper/Section2TauRepresentation.lean); [`LeanPaper.Section2RationalDomains.tauDomain_iff_denom_dvd`](../src/LeanPaper/Section2RationalDomains.lean) |
| pencil — Actual affine pencil, determinant, Gram matrix and direction | **Constructed and retained.** The residue-defined rational pencil, determinant delta, evaluated real Gram matrix and derivative matrix are actual definitions. The positive analytic moment realization is proved for admissible odd-weight parameters. **Remaining:** Later modified beta/multiweight families and their analytic measures must be constructed separately. Sources: [`ManuscriptChain.Real.pencil`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.delta`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.gram`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.Real.derivativeMatrix`](../src/Definition_2_1_Order_s_Rational_Moment_Functional.lean); [`ManuscriptChain.REALIZATION`](../src/MAIN_CHAIN_ASSEMBLED.lean) |
| primitive — Primitive integer polynomial | **Constructed and retained.** A nonzero rational determinant is normalized by clearing denominators, removing content and fixing a positive scale; an actual primitive Z-polynomial, degree and center positivity are proved. **Remaining:** The legacy rational-valued P_prim and the constructed integer polynomial are not counted as separate paper theorems. Quantitative integral multipliers/height bounds remain open. Sources: [`ManuscriptChain.BasisInvariance.primitiveNormalization`](../src/Theorem_2_4_Canonical_Basis_Invariance.lean); [`ManuscriptChain.GeneralIrrationality.primitivePolynomial`](../src/MAIN_CHAIN_IRRATIONALITY.lean); [`ManuscriptChain.GeneralIrrationality.primitivePolynomial_isPrimitive`](../src/MAIN_CHAIN_IRRATIONALITY.lean) |
| spectral — Normalized spectral matrix and exact norm radius | **Constructed and verified.** The actual whitening matrix is (sqrt G)^(-1) M (sqrt G)^(-1), with Euclidean operator norm. The new endpoint identifies the retained spectral-factor radius with inverse norm and transports to the actual primitive polynomial. **Remaining:** No missing definition or norm bridge for Theorem 3.1. Later exponential estimates remain open. Sources: [`LeanPaper.OperatorNormDisk.whitened`](../src/LeanPaper/OperatorNormDisk.lean); [`ManuscriptChain.General.zeroFreeRadius`](../src/Theorem_3_1_General_Odd_Weight_Endpoint.lean); [`LeanPaper.PrimitiveNormDisk.primitive_theorem_3_1`](../src/LeanPaper/PrimitiveNormDisk.lean) |
| reciprocal — Reciprocal root moments and Hankel matrices | **Constructed and retained.** The actual root vector, inverse-square atoms, finite moments, coalesced support/multiplicities and Hankel matrices are defined. Their finite-support positivity/rank laws are proved. **Remaining:** The corrected finite objects do not validate literal all-order strict positivity. Higher logarithmic-moment identification remains separately open. Sources: [`LeanPaper.ReciprocalRootMoments.manuscriptRoots`](../src/LeanPaper/ReciprocalRootMoments.lean); [`LeanPaper.ReciprocalRootMoments.reciprocalEvenMoment`](../src/LeanPaper/ReciprocalRootMoments.lean); [`LeanPaper.ReciprocalRootMoments.reciprocalHankel`](../src/LeanPaper/ReciprocalRootMoments.lean) |
| dual — Dual rational coefficient pencil | **Finite construction retained.** Actual rational dual constants, entries and determinant, with coefficient-Gram slope and its spectral theorem under row separation. **Remaining:** The continuous Beukers measures and infinite Krein subspaces/analytic identifications are not thereby constructed; see 5.1-5.3 and 6.7/6.17. Sources: [`ManuscriptChain.Real.dualConstant`](../src/LeanPaper/ImportedSection56/DualMoments.lean); [`ManuscriptChain.Real.dualEntry`](../src/LeanPaper/ImportedSection56/DualMoments.lean); [`ManuscriptChain.Real.dualDelta`](../src/LeanPaper/ImportedSection56/DualMoments.lean) |
| quantitative_inputs — Decay and comparison targets | **Defined hypotheses; not supplied witnesses.** Named normalized quadratic decay, local comparison and index-budget propositions make the missing arithmetic inputs explicit. **Remaining:** These definitions are obligations rather than proofs. No accepted family-specific decay/height witness or unconditional odd-zeta irrationality endpoint is supplied. Sources: [`ManuscriptChain.GeneralIrrationality.NormalizedQuadraticDecay`](../src/MAIN_CHAIN_IRRATIONALITY.lean); [`ManuscriptChain.RealTransfer.LocalComparison`](../src/Theorem_4_1_Spectral_Irrationality_Measure_Criterion.lean); [`ManuscriptChain.RealTransfer.IndexBudget`](../src/Theorem_4_1_Spectral_Irrationality_Measure_Criterion.lean) |

## Individual results

| Item | Classification | Proved scope and exact boundary |
| --- | --- | --- |
| 2.2 — Rational functional pullback | Partially formalized | Pointwise substitution outside the finite pole set is connected to the canonical polynomial-plus-simple-pole moment formula, including the whole polynomial quotient and vanishing lower moments. Equality in the actual RatFunc field now forces equality of polynomial parts/residues across different supports; mu descends to a representation-independent functional on precisely the denominator-divisibility simple-negative-square-pole domain. **Remaining:** Lift mu/tau linearity to the RatFunc subspaces, define and identify the actual RatFunc pullback substitution operator, and assemble the literal function-level identity. The algebraic simple-pole domain and representation independence are now proved; no meromorphic-domain equivalence is claimed. |
| 2.3 — Reflection and difference identities for Tau | Partially formalized | Finite polynomial-plus-simple-pole reflection and tau difference, including the degree-2k correction coefficient and the matching pointwise x-to-x+1 translation. Tau, reflected moments and translated moments are now representation-independent in RatFunc; the full algebraic integer-simple-pole domain is characterized by denominator divisibility. **Remaining:** Lift linearity and construct the RatFunc reflection/translation substitutions, retaining their domain exclusions, to assemble the complete function-level reflection/difference theorem. Algebraic domain characterization is no longer an open gap. |
| 2.4 — Canonical basis invariance | Partially formalized | Rational matrix basis transport scales the determinant by det(A)det(B); positive primitive integer normalizations are constructed and are invariant up to sign. **Remaining:** The printed theorem quantifies over an arbitrary Q[X]-valued linear functional and arbitrary polynomial bases. An explicit transport from those functional evaluations/bases to changeBasisPencil is still needed; matrix transport alone is not that whole statement. |
| 2.5 — Lagrange pole diagonalization | Partially formalized | Constructed Lagrange polynomials have Kronecker evaluations and inverse-Vandermonde coefficients; their actual transformed pencil has constant off-diagonal entries, explicit diagonal slope, and nonzero slope determinant. **Remaining:** Connect the coefficient-transport entries to the printed general functional expression mu_X(D_N^(2m) L_a L_b / D_K), including the rational-domain bridge. The finite polynomial and matrix identities are already retained. |
| 3.1 — Universal hyperbolicity and zero-free disk | Verified | Complete actual determinant and primitive integer-polynomial hyperbolicity: constructed primitive normalization, exact degree h, true Riemann-zeta center, positive center evaluation, all complex roots real and distinct from the center, and the literal Euclidean inverse-operator-norm zero-free disk. The constructed spectral radius equals &#124;&#124;G^(-1/2) M G^(-1/2)&#124;&#124; and a root attains the boundary. **Remaining:** None for Theorem 3.1. Pairwise root distinctness is not claimed by the printed theorem or this formalization. Exponential spectral estimates and irrationality belong to later items and remain open. |
| 3.2 — Continuous hyperbolic pencil for all real s > 1 | Partially formalized | Positive real-power residue scaling preserves signs and slope nonsingularity; a supplied positive-definite base gives a real spectrum. **Remaining:** Construct and identify the continuous real-s moment integral and prove positivity of the actual real-s base matrix. |
| 3.3 — Total positivity, leading sign, universal signature | Partially formalized | Actual Gram determinant positivity, exact leading-coefficient residue product and weight-invariant positive/negative residue index sets. **Remaining:** Arbitrary mixed-minor strict total positivity, Stieltjes determinacy and exact manuscript inertia/root-count formulas are not assembled. |
| 3.4 — Root interlacing and Dodgson condensation | Blocked | All zeros of every actual principal determinant are real even with singular slope. The actual admissible k=2,m=1,N=1,K=6 first minor is a positive constant and has no roots. The corrected actual principal determinant degree and number of real roots counted with multiplicity are now proved equal to the rank of its direction matrix, allowing singular slopes. **Remaining:** The literal universal r-root enumeration/closest-root minimum is false. The corrected degree/rank and root-count laws are proved; rank-sensitive interlacing and all-rank Dodgson assembly remain open. |
| 3.5 — Stieltjes J-fraction from interlacing roots | Blocked | Correct normalized two- and three-level determinant, continuant and Schur-fraction identities for I+tB. An explicit general scalar diagnostic disproves the unscaled normalized-fraction calculation; it is not claimed to be a manuscript-family instance. **Remaining:** The literal displayed fraction has inconsistent normalization. The general Lanczos/Jacobi construction, cyclicity/strict off-diagonal claims, determinant-ratio normalization and spectral-edge growth are unproved. |
| 3.6 — Stieltjes reciprocal-root power sums | Blocked | Actual reciprocal-root even moments are finite positive atomic moments; repeated inverse-square gaps are coalesced. Hankel strict positivity holds exactly up to distinct support size and determinants vanish above it. An attained maximum U satisfies U^m <= sum u_i^m <= h*U^m. At any rational non-root shift the actual nearest-root distance is attained; the correctly oriented negative-root-power bound and convergence to that distance are proved. First inverse-gap and second even moments are rational, with the correct first and second logarithmic derivative formulas. The actual Hankel determinant at order h+1 is explicitly zero. **Remaining:** The literal all-order strict Hankel positivity and printed bound/sign remain blocked. Rationality and logarithmic-derivative identification at all orders m>=3 remain open. First/second log identities are stated for delta; an explicit primitive-polynomial log specialization remains separate, although its root set is identified. The fixed-family inner limit supplies no uniform large-K collapse/separation estimate. |
| 3.7 — Turanian non-negativity and Newton log-concavity | Partially formalized | For the actual primitive integer polynomial, every derivative order satisfies Turan nonnegativity; nonconstant orders are strictly positive off roots, with equality exactly at a simultaneous zero of the derivative and its next derivative. The complete weak binomial-normalized Newton coefficient hierarchy, arbitrary real translated hierarchy and zeta-centered normalized Taylor hierarchy are proved, together with the weak strengthened degree-normalized Laguerre bound. **Remaining:** The strict strengthened center bound, strict normalized Newton inequalities/equality classification, and the actual shifted-coefficient nonvanishing/generic-distinctness claims remain open. These are not consequences of the proved weak hierarchy alone. |
| 3.8 — Christoffel-Darboux pole representation and Jacobi derivative | Partially formalized | Actual relative/pole matrices share characteristic polynomial and trace. Affine determinant/logarithmic Jacobi derivative and exact polynomial Taylor remainder are proved. **Remaining:** Complete orthogonal-polynomial Christoffel-Darboux identification and the stated asymptotic remainder estimate remain unproved. |
| 3.9 — Hurwitz and Dirichlet hyperbolicity | Partially formalized | Shifted negative-square pole algebra and real-power slope scaling; positivity of five explicit Fekete numerators/rational kernels; positive residues give positive slopes. **Remaining:** Actual Hurwitz/Dirichlet Mellin moment evaluation and analytic Gram realization remain unconstructed. |
| 4.1 — Spectral irrationality measure criterion | Partially formalized | Integer-polynomial rational-approximation transfer and spectral local-comparison lemmas; a constructed primitive odd-zeta family has a conditional irrationality transfer. **Remaining:** Derive the printed asymptotic index-budget selection from its hypotheses and connect all decay/local-comparison rates to the actual family. No concrete odd-zeta decay estimate has been supplied. |
| 4.2 — Transfer for algebraic approximations | Partially formalized | A nonzero integer cannot equal a product of complex quantities whose norm is strictly below one. **Remaining:** Construct the actual resultant and exact product identity, prove nonvanishing, and establish bounded-degree height and smallness estimates. |
| 4.3 — Ultrametric zero-free disk | Already proved and retained | The complete printed integer-polynomial C_p zero-free disk: at any integral p-adic center with nonzero value, the polynomial norm is preserved at every C_p point in the open disk of that value norm. **Remaining:** None for Proposition 4.3 itself. Family-specific p-adic zeta identification, valuations and irrationality are outside its printed statement. |
| 4.4 — Spectral bound and irrationality measure for zeta(5) | Partially formalized | Only a conditional comparison between historical spectral exponent targets is proved; there is no retained concrete zeta(5) spectral bound or irrationality measure. **Remaining:** Actual normalization/arithmetic multiplier, determinant decay and spectral bound remain open. Prove the paper value 11.411 and its effective measure; historical 11.407/10.954 are distinct targets. |
| 4.5 — Irrationality and measure for b*zeta(5)+a*zeta(3) | Partially formalized | Coupled-shift algebra and general odd-weight/linear-family transfer infrastructure are retained. **Remaining:** Construct the actual b*zeta(5)+a*zeta(3) positive density cone, p-adic cancellation, uniform growth and quantitative measure inputs. |
| 4.6 — Determinant bounds and coefficient heights | Partially formalized | Actual primitive leading coefficient equals center value times the relative determinant; a finite upper bound on that ratio gives a reciprocal lower bound for the center value. **Remaining:** Uniform determinant/height-decay and asymptotic constants are unproved. Paper constants 0.23310 and 3.73980 remain distinct from historical 0.23338 and 3.73872. |
| 4.7 — Root collapse and separation | Partially formalized | A finite cap-and-average counting inequality applies to actual spectral log magnitudes; a factor above threshold gives an actual root within the corresponding exponential radius. **Remaining:** Prove uniform spectral caps, average lower bounds and the actual asymptotic collapse/separation constants. |
| 4.8 — Rational root exclusion and cluster degree bounds | Partially formalized | Finite rational/integer factor-distance upper and lower bounds and actual primitive-polynomial data. **Remaining:** Effective family-wide coefficient/height budgets, nonvanishing, and uniform rational-root exclusion/cluster-degree estimates remain open. |
| 5.1 — Two-variable Beukers measure for zeta(7) | Partially formalized | Actual dual rational moments, affine entries and determinant; exact symmetry and coefficient-Gram slope C*C^T. **Remaining:** Continuous two-variable Beukers measure evaluation, convergence and identification with these rational moments are not constructed. |
| 5.2 — Dual hyperbolicity and Krein decomposition | Partially formalized | Coefficient-Gram SOS/nullspace and row-separation positivity, actual dual degree/real spectrum, basis/weight invariance, finite Krein identities/cones. A genuine zeta(7)<38/37 estimate proves the explicit 37X-38 witness is negative at true zeta(7). **Remaining:** Continuous/infinite Krein decomposition, constructed general positive/negative subspaces and tail admissions remain open. The rank-one sign does not prove the paper-wide cones or irrationality. |
| 5.3 — Beukers measure and dual pencil for beta(4) | Partially formalized | Finite two/three-node beta Gram strictness, tensor-grid identities and orientation-corrected residue positivity. **Remaining:** Construct the continuous beta(4) Beukers measure and identify the actual dual moments/pencil and full claimed spectrum. |
| 5.4 — Higher-zeta cancellation on even pole pairs | Partially formalized | Simple-pole pullback and even pole-pair generator identities are retained. **Remaining:** Extend to the full manuscript rational functional by representation independence/linearity and prove the stated higher-zeta cancellation with exact pole restrictions. |
| 5.6 — Weight-seven prime-sum evaluation and pole refinement | Not formalized | No mapped active proof of this complete result or its specific prime-sum integrals. **Remaining:** Construct the piecewise floor-function prime sums, prove the exact outer integral 453803/288000, inner tail bounds/prime-sum limit and pole-ordered residue refinement. |
| 5.7 — Double-pole determinant for 1,zeta(5),zeta(6) | Not formalized | No mapped active proof of the simultaneous double-pole determinant. **Remaining:** Construct the explicit double-pole partial fractions and functional, prove q-adic valuation v_q(J_(2m))=-36m for the stated primes, and the local minor valuation lower bound. |
| 6.1 — Divided-difference valuation and intrinsic p^-6 barrier | Not formalized | No mapped active proof of the complete divided-difference/valuation result. **Remaining:** Prove the two-variable to Mellin integral change of variables, off-diagonal harmonic divided-difference valuation -7, and invertible local pole obstruction block for the actual family. |
| 6.2 — Simultaneous weight-(6,7) Beukers functional | Not formalized | No mapped active proof of the simultaneous weight-(6,7) integral formula. **Remaining:** Evaluate the shifted Beukers moments, derive the exact zeta(7)/zeta(6) linear form, and prove the common denominator 6*d_K^7 with no added overhead. |
| 6.3 — q-adic nonvanishing and positive-cone approximations | Not formalized | No mapped active proof of the stated q-adic determinant or explicit infinite-cone approximation family. **Remaining:** For A_rho=x^rho+x^(rho+q), prove valuation -7q and rational nonvanishing; construct the negative-mode annihilating subspace, dimension bound, positive evaluation and exponential determinant decay. |
| 6.4 — Character-Vandermonde sign cancellation and beta hyperbolicity | Partially formalized | Raw alternating character/Vandermonde sign and its corrected normalization, finite positive residues and finite beta Gram strictness. **Remaining:** Identify the actual analytic character-weight moment measure/pencil and prove the q-adic nonvanishing and full claimed hyperbolicity statement. Raw sign at odd N must be retained. |
| 6.5 — q-adic nonvanishing at zero | Not formalized | No mapped active proof of the actual beta determinant valuation at zero. **Remaining:** For q>7 and q=1 mod 8 with the specified N,K, prove v_q(Delta_K(0))=-(3m_q-2), including exact local residue/minor arithmetic. |
| 6.6 — Generalized multi-weight positive-definite pencil | Partially formalized | Finite positive matrix cones and nonnegative semidefinite cones with a positively weighted positive-definite anchor give positive direction, exact finite degree, real spectrum and Turan inequalities. **Remaining:** Construct the actual infinite multiweight density, uniform two-sided analytic comparison, arithmetic multiplier and universal signature/asymptotic claims. |
| 6.7 — Universal multi-weight Beukers Krein decomposition | Not formalized | No active manuscript-equivalent universal multiweight Beukers construction. **Remaining:** Construct the actual multiweight signed measure, its moment identity and coefficient Gram bridge; prove infinite-rank Krein positive/negative subspaces and arithmetic nonvanishing. The weight-seven finite algebra of 5.2 is not this general theorem. |
| 6.8 — Three-term linear-independence cone | Not formalized | No active proof of the unconditional three-term linear-independence cone. **Remaining:** Construct the actual cone/linear-form approximants and all arithmetic nonvanishing, height and decay estimates needed to deduce independence of 1,zeta(3),zeta(5). |
| 6.9 — Triple-pole and multi-weight determinants | Partially formalized | Finite triple-pole Hermite-jet functional multiplication, block congruence and determinant factorization/nonvanishing. **Remaining:** Prove exact global pole order, actual-family distinct-node Hermite-table invertibility and nonzero local factors, then q-adic/arithmetic transfer. |
| 6.10 — Potential-gap identity and quadratic derivative growth | Partially formalized | Finite centered/normalized determinant, leading coefficient and relative/symmetric spectral determinant identities, including constructed positive square root. **Remaining:** Prove the asymptotic positive potential gap and quadratic derivative-growth limits for the stated one/two-variable families. |
| 6.11 — Distribution growth and 2-adic quotient obstruction | Not formalized | No active proof of the distribution growth law or complete dyadic quotient obstruction. **Remaining:** Prove Euler distribution identities, local prime weights and their growth in k, the archimedean rate independence, and the exact 2-adic polynomial-quotient leading coefficient/valuation obstruction. |
| 6.12 — Full-dimension sign-flip positivity and q-adic nonvanishing | Not formalized | No active proof of full-dimension sign-flip restoration for actual beta(4). **Remaining:** Construct the sign-flipped actual pencil, prove oriented slope, construct rational cutoffs sufficiently close to the sign-change point to establish full Gram positivity, and preserve exact q-adic nonvanishing. |
| 6.13 — Central-factorial secant differential identity | Not formalized | No active proof of the central-factorial secant differential identity or its analytic consequences. **Remaining:** Prove the differential identity, Laplace-mode annihilation/convergence and positive accelerated weight; identify the coupled actual pencil and prove the stated unilateral signature. |
| 6.14 — Even-pole cosh scaling and coupled pencils | Not formalized | No active proof of the even-pole beta/cosh analytic scaling and coupled zeta-beta theorem. **Remaining:** Prove exact beta even-pole/moment formulas and cosh scaling, uniform positive comparison constants, coupled-pencil identification/signature and the claimed exponential disk estimates. |
| 6.15 — Arithmetic transcendence, positive measure and rank-one law | Not formalized | No active proof of the full odd-beta arithmetic/measure/rank-one result. **Remaining:** Identify odd beta values as nonzero rational multiples of odd powers of pi; establish the claimed effective measures, continuous positive moments and total positivity; connect the rank-one pencil and prove its geometric convergence asymptotic. |
| 6.16 — Generalized multi-weight Zeta-Beta pencil | Not formalized | No active proof of the full multiweight Zeta-Beta positive-density construction. **Remaining:** Construct its actual combined analytic density and moment/pencil identity; prove positivity-cone comparison, universal signature and quantitative/arithmetic conclusions. Finite cone modules do not instantiate these data. |
| 6.17 — Universal two-variable Zeta-Beta pencil | Not formalized | No active proof of the universal two-variable Zeta-Beta theorem. **Remaining:** Construct actual coupled signed measures and moments, full-rank coefficient slope with growth control, infinite Krein subspaces and highest-weight q-adic determinant valuations. |
| 6.18 — Principal-minor 2-adic integrality and dyadic heights | Not formalized | No active proof of the full principal-minor dyadic integrality/height and effective-measure theorem. **Remaining:** Prove the exact sub-threshold quotient disappearance and pole integrality, full-dimension dyadic height loss and odd-prime multiplier estimates, then the printed measure 25687 for the stated cones. Historical degree/quotient lemmas are not an active proof of these arithmetic claims. |

## Dependency endpoints and hypotheses

The machine-readable [formalization_status.json](formalization_status.json) preserves all 45 IDs/order and records source hashes, retained/new endpoints, exact hypotheses and proposed ledger changes. The endpoint lists are representative dependencies; a name alone is not a complete statement certificate.

**2.2.** k >= 1; finitely supported canonical coefficients; evaluation away from the specified poles.

- [`LeanPaper.PullbackReflection.function_and_moment_pullback`](../src/LeanPaper/PullbackReflection.lean)
- [`LeanPaper.Section2RepresentationIndependence.muFunctionalPoly_representation_independent`](../src/LeanPaper/Section2RepresentationIndependence.lean)
- [`LeanPaper.Section2RationalDomains.muDomain_iff_denom_dvd`](../src/LeanPaper/Section2RationalDomains.lean)

**2.3.** k >= 1; finite support; the difference theorem excludes pole labels 0 and 1.

- [`LeanPaper.PullbackReflection.finite_span_reflection`](../src/LeanPaper/PullbackReflection.lean)
- [`LeanPaper.Section2FiniteDifference.function_and_moment_difference`](../src/LeanPaper/Section2FiniteDifference.lean)
- [`LeanPaper.Section2TauRepresentation.tauFiniteSpan_representation_independent`](../src/LeanPaper/Section2TauRepresentation.lean)
- [`LeanPaper.Section2TauRepresentation.translatedMoment_representation_independent`](../src/LeanPaper/Section2TauRepresentation.lean)
- [`LeanPaper.Section2RationalDomains.tauDomain_iff_denom_dvd`](../src/LeanPaper/Section2RationalDomains.lean)

**2.4.** Invertible rational change matrices and nonzero determinant polynomial. Normalization existence is proved, not assumed.

- [`ManuscriptChain.BasisInvariance.det_changeBasisPencil`](../src/Theorem_2_4_Canonical_Basis_Invariance.lean)
- [`ManuscriptChain.BasisInvariance.theorem_2_4_constructed_canonical_basis_invariance`](../src/Theorem_2_4_Canonical_Basis_Invariance.lean)

**2.5.** Actual negative-square pole nodes and finite manuscript parameter data; invertibility/nonzero residues are proved.

- [`LeanPaper.Section2LagrangeIdentification.archive_polynomial_eq_constructed`](../src/LeanPaper/Section2LagrangeIdentification.lean)
- [`LeanPaper.Section2LagrangeBridge.actual_lagrange_slope`](../src/LeanPaper/Section2LagrangeBridge.lean)
- [`ManuscriptChain.PoleDiagonalization.theorem_2_5_lagrange_pole_diagonalization`](../src/Theorem_2_5_Lagrange_Pole_Diagonalization.lean)

**3.1.** k,m,N >= 1 and N < K. No supplied integral identity, Gram-positivity certificate, or arithmetic estimate. The paper says roots are distinct from the center, not pairwise distinct.

- [`ManuscriptChain.MAIN_CHAIN_UNCONDITIONAL`](../src/MAIN_CHAIN_ASSEMBLED.lean)
- [`ManuscriptChain.EXACT_ZERO_FREE_DISK`](../src/MAIN_CHAIN_ASSEMBLED.lean)
- [`ManuscriptChain.GeneralIrrationality.primitivePolynomial_natDegree`](../src/MAIN_CHAIN_IRRATIONALITY.lean)
- [`LeanPaper.OperatorNormDisk.actual_radius_eq_inverse_norm`](../src/LeanPaper/OperatorNormDisk.lean)
- [`LeanPaper.PrimitiveNormDisk.primitive_theorem_3_1`](../src/LeanPaper/PrimitiveNormDisk.lean)
- [`LeanPaper.PrimitiveNormDisk.primitive_exact_norm_disk`](../src/LeanPaper/PrimitiveNormDisk.lean)

**3.2.** Real exponent algebra on the finite nodes; base symmetry and positive definiteness remain explicit hypotheses.

- [`PaperAdvances.Proposition3_2.slope_det_ne_zero`](../src/LeanPaper/ImportedSection3/RealExponent.lean)
- [`PaperAdvances.Proposition3_2.all_complex_roots_real`](../src/LeanPaper/ImportedSection3/RealExponent.lean)

**3.3.** Admissible actual odd-weight Gram matrix where used; sign products/index-set equalities do not by themselves prove inertia counts.

- [`PaperAdvances.Theorem3_3.actual_gram_det_pos`](../src/LeanPaper/ImportedSection3/SignStructure.lean)
- [`PaperAdvances.Theorem3_3.leading_coefficient_product`](../src/LeanPaper/ImportedSection3/SignStructure.lean)
- [`PaperAdvances.Theorem3_3.positive_pole_count_constant`](../src/LeanPaper/ImportedSection3/SignStructure.lean)

**3.4.** Admissible actual parameters and any injective principal-index selection. The counterexample is an actual family instance.

- [`LeanPaper.PrincipalMinorRealRoots.original_principal_zeros_real`](../src/LeanPaper/PrincipalMinorRealRoots.lean)
- [`LeanPaper.SingularPrincipalMinorExample.first_minor_no_real_zero`](../src/LeanPaper/SingularPrincipalMinorExample.lean)
- [`LeanPaper.SingularPrincipalMinorExample.first_minor_natDegree_zero`](../src/LeanPaper/SingularPrincipalMinorExample.lean)
- [`LeanPaper.PrincipalMinorRank.original_principal_degree_eq_rank`](../src/LeanPaper/PrincipalMinorRank.lean)
- [`LeanPaper.PrincipalMinorRank.original_principal_real_roots_card_eq_rank`](../src/LeanPaper/PrincipalMinorRank.lean)

**3.5.** Finite real scalar entries; Schur denominators are nonzero where divided by.

- [`LeanPaper.Section3ContinuedFractions.corollary_3_5_two_level_schur_identity`](../src/LeanPaper/ImportedSection3/NormalizedContinuedFraction.lean)
- [`LeanPaper.Section3ContinuedFractions.normalized_three_schur_identity`](../src/LeanPaper/ImportedSection3/NormalizedContinuedFraction.lean)
- [`LeanPaper.ManuscriptObstructions.normalized_fraction_printed_formula_fails`](../src/LeanPaper/ManuscriptObstructions.lean)

**3.6.** For positive reciprocal atoms the shift is not a root. Repeated roots and equal squared gaps are allowed. Nearest-root convergence/rationality use rational q with delta(q) != 0; first/second derivative statements use an arbitrary real non-root point. No simplicity assumption.

- [`LeanPaper.ReciprocalRootMoments.manuscript_reciprocal_moments`](../src/LeanPaper/ReciprocalRootMoments.lean)
- [`LeanPaper.ReciprocalRootMoments.reciprocalHankel_det_pos_iff`](../src/LeanPaper/ReciprocalRootMoments.lean)
- [`LeanPaper.Section3RootMomentBounds.actual_reciprocal_moment_bounds`](../src/LeanPaper/ImportedSection3/RootMomentBounds.lean)
- [`LeanPaper.ReciprocalNearestRootLimit.actual_nearest_root_limit`](../src/LeanPaper/ReciprocalNearestRootLimit.lean)
- [`LeanPaper.ReciprocalLogDerivative.actual_first_inverse_gap_sum_rational`](../src/LeanPaper/ReciprocalLogDerivative.lean)
- [`LeanPaper.ReciprocalLogDerivative.actual_log_hasDerivAt`](../src/LeanPaper/ReciprocalLogDerivative.lean)
- [`LeanPaper.ReciprocalSecondMoment.actual_second_moment_rational`](../src/LeanPaper/ReciprocalSecondMoment.lean)
- [`LeanPaper.ReciprocalSecondMoment.actual_log_second_hasDerivAt`](../src/LeanPaper/ReciprocalSecondMoment.lean)
- [`LeanPaper.ManuscriptObstructions.manuscript_hankel_det_succ_eq_zero`](../src/LeanPaper/ManuscriptObstructions.lean)
- [`LeanPaper.ManuscriptObstructions.manuscript_hankel_not_positive_at_all_orders`](../src/LeanPaper/ManuscriptObstructions.lean)
- [`LeanPaper.ManuscriptObstructions.first_logarithmic_ratio_sign_fails`](../src/LeanPaper/ManuscriptObstructions.lean)

**3.7.** Actual admissible parameters. Turan nonnegativity holds for every derivative order; strictness/equality use k<h and the off-root condition where stated. Newton uses the full degree h and interior coefficient range k+2<=h, with no coefficient sign or root-simplicity assumption.

- [`PaperAdvances.Theorem3_7_AllDegrees.THEOREM_3_7_ACTUAL_ALL_DEGREES`](../src/LeanPaper/ImportedSection3/AllDegreeTuran.lean)
- [`PaperAdvances.Theorem3_7_StrictRolle.THEOREM_3_7_ACTUAL_TURAN_STRICT`](../src/LeanPaper/ImportedSection3/StrictTuranRolle.lean)
- [`LeanPaper.Section3Newton.cubic_newton_first`](../src/LeanPaper/ImportedSection3/CubicNewton.lean)
- [`LeanPaper.HigherDerivativeTuran.actual_primitive_all_derivative_turan`](../src/LeanPaper/HigherDerivativeTuran.lean)
- [`LeanPaper.HigherDerivativeTuran.actual_primitive_all_derivative_turan_strict`](../src/LeanPaper/HigherDerivativeTuran.lean)
- [`LeanPaper.HigherDerivativeTuran.actual_primitive_all_derivative_turan_equality`](../src/LeanPaper/HigherDerivativeTuran.lean)
- [`LeanPaper.NormalizedNewton.actual_primitive_laguerre`](../src/LeanPaper/NormalizedNewton.lean)
- [`LeanPaper.NormalizedNewton.actual_primitive_coefficient_newton`](../src/LeanPaper/NormalizedNewton.lean)
- [`LeanPaper.NormalizedNewton.actual_primitive_shifted_newton`](../src/LeanPaper/NormalizedNewton.lean)
- [`LeanPaper.NormalizedNewton.actual_primitive_centered_newton`](../src/LeanPaper/NormalizedNewton.lean)

**3.8.** The inverse and logarithm identities retain determinant/nonvanishing hypotheses.

- [`PaperAdvances.Theorem3_8_Actual.actual_relative_charpoly_eq_pole`](../src/LeanPaper/ImportedSection3/ActualPoleKernel.lean)
- [`PaperAdvances.Theorem3_8_Jacobi.actual_affine_log_jacobi`](../src/LeanPaper/ImportedSection3/Jacobi.lean)
- [`PaperAdvances.Theorem3_8_ExactTaylor.affine_det_exact_second_order`](../src/LeanPaper/ImportedSection3/ExactTaylor.lean)

**3.9.** Generic shifted spectral theorem assumes a symmetric positive-definite base. Finite kernel positivity does not discharge the analytic identification.

- [`PaperAdvances.Theorem3_9_ShiftedPole.hurwitz_complex_roots_real`](../src/LeanPaper/ImportedCharacter/ShiftedPole.lean)
- [`PaperAdvances.Theorem3_9_CharacterPositive.all_rational_character_kernels_pos`](../src/LeanPaper/ImportedCharacter/CharacterPositive.lean)

**4.1.** Explicit Decay, LocalComparison and IndexBudget in the measure theorem; NormalizedQuadraticDecay and unboundedness for the odd-zeta transfer. These are substantive unproved family inputs.

- [`ManuscriptChain.RealTransfer.conditional_measure`](../src/Theorem_4_1_Spectral_Irrationality_Measure_Criterion.lean)
- [`ManuscriptChain.GeneralIrrationality.irrational_zeta_of_normalized_decay`](../src/MAIN_CHAIN_IRRATIONALITY.lean)

**4.2.** A nonzero integer resultant value, exact product identity and product-norm upper bound are supplied hypotheses.

- [`PaperOrder.Section4.proposition_4_2_resultant_product_barrier`](../src/LeanPaper/ImportedSection4/Proposition_4_2_Resultant_Product_Barrier.lean)

**4.3.** p prime, Q in Z[X], xi in Z_p, Q(xi) != 0, alpha in C_p and |alpha-xi|_p < |Q(xi)|_p. These are exactly the printed premises, not missing proof obligations.

- [`PaperAdvances.Proposition4_3_ComplexPadicDisk.PROPOSITION_4_3_INTEGER_COMPLEX_PADIC`](../src/LeanPaper/ImportedSection4/Proposition_4_3_ComplexPadicDisk.lean)

**4.4.** The stronger historical spectral estimate is assumed. Comparing exponentials does not establish either estimate.

- [`PaperChain.stage06_sharpened_implies_standard`](../src/PaperChain/Stage06.lean)

**4.5.** The source definitions of a weight sandwich/positivity cone are not proofs that the actual density lies in it.

- [`PaperChain.stage07_coupled_shift`](../src/PaperChain/Stage07.lean)
- [`ManuscriptChain.GeneralArithmetic.linearFamily_degree`](../src/Theorem_4_1_Linear_Odd_Zeta_Family.lean)

**4.6.** The ratio upper bound is an explicit finite hypothesis, not an established family estimate.

- [`LeanPaper.Section4ManuscriptBridge.primitive_leading_barrier_identity`](../src/LeanPaper/Section4ManuscriptBridge.lean)
- [`LeanPaper.Section4ManuscriptBridge.primitive_evaluation_lower_of_inverse_ratio_bound`](../src/LeanPaper/Section4ManuscriptBridge.lean)

**4.7.** The spectral cap and average bounds are supplied; the finite conversion is proved.

- [`LeanPaper.Section4ManuscriptBridge.manuscript_spectral_cluster_fraction`](../src/LeanPaper/Section4ManuscriptBridge.lean)
- [`LeanPaper.Section4ManuscriptBridge.manuscript_large_exponent_gives_close_root`](../src/LeanPaper/Section4ManuscriptBridge.lean)

**4.8.** Finite factorization and bound hypotheses are explicit; no asymptotic budget is constructed.

- [`PaperOrder.Section4.proposition_4_8_factor_evaluation_bounds`](../src/LeanPaper/ImportedSection4/Proposition_4_8_Factor_Distance_Bounds.lean)

**5.1.** Finite polynomial coefficient arrays and explicit rational moment formulas; a definition matching the desired moments is not a proof of the integral formula.

- [`PaperOrder.CoreAlgebra.dualSlopeMatrix_eq_CCT`](../src/LeanPaper/ImportedSection56/DualPencilCCT.lean)
- [`PaperOrder.CoreAlgebra.dualPencil_decomposition`](../src/LeanPaper/ImportedSection56/DualPencilCCT.lean)

**5.2.** Row separation/full coefficient rank where required; selected monomial families discharge it. Finite Krein cone hypotheses remain explicit.

- [`LeanPaper.Section5DualSpectrum.actual_dual_zeros_real`](../src/LeanPaper/Section5DualSpectrum.lean)
- [`PaperOrder.PrincipalTheorems.finiteKreinGram_posDef`](../src/LeanPaper/ImportedSection56/FiniteKreinCone.lean)
- [`PaperOrder.PrincipalTheorems.weightSeven_rankOne_negative_unconditional`](../src/LeanPaper/ImportedSection56/ZetaSevenBound.lean)

**5.3.** Positive finite node weights and injective evaluation data; the two/three-node cases supply their finite injectivity.

- [`PaperChronology.Paper10.PAPER10_BETA_BILINEAR_TENSOR_GRID_STRICT`](../src/LeanPaper/Section6BetaFinite.lean)
- [`PaperChronology.Paper10.PAPER10_BETA_THREE_NODE_PENCIL_STRICT`](../src/LeanPaper/Section6BetaFinite.lean)

**5.4.** Simple poles and k>=1; unsupported higher-order poles are not silently admitted.

- [`Zetahyperbolic.pullback_identity_pole`](../src/Zetahyperbolic/Section2Checked.lean)

**6.4.** Positive finite weight/evaluation assumptions are explicit; normalization removes the raw (-1)^N orientation rather than proving it was always positive.

- [`PaperChronology.Paper10.PAPER10_BETA_VANDERMONDE_RESIDUAL_SIGN`](../src/LeanPaper/Section6BetaFinite.lean)
- [`PaperChronology.Paper10.PAPER10_BETA_NORMALIZED_RESIDUES_POSITIVE`](../src/LeanPaper/Section6BetaFinite.lean)

**6.6.** Finite component PSD/PD and coefficient nonnegativity/positive anchor are assumptions; no infinite analytic density is instantiated.

- [`PaperAdvances.Theorem6_6_FiniteMultiweightCone.FINITE_MULTIWEIGHT_SPECTRAL_HYPERBOLICITY`](../src/LeanPaper/ImportedMultiweight/FiniteMultiweightCone.lean)
- [`PaperAdvances.Theorem6_6_AnchoredSemidefiniteCone.ANCHORED_FINITE_CONE_SPECTRAL_PACKAGE`](../src/LeanPaper/ImportedMultiweight/AnchoredSemidefiniteCone.lean)

**6.9.** The nonzero Hermite-table determinant and highest local jet/block coefficients remain explicit hypotheses.

- [`Zetahyperbolic.TriplePoleRepair.hermite_congruence`](../src/LeanPaper/ImportedSection56/TriplePoleHermite.lean)
- [`Zetahyperbolic.TriplePoleRepair.momentMatrix_det_ne_zero`](../src/LeanPaper/ImportedSection56/TriplePoleHermite.lean)

**6.10.** Finite positive-definite base and nonzero scale/direction where degree is asserted; no large-K growth estimate follows from the identity alone.

- [`Zetahyperbolic.Theorem6_10.abs_leadingCoeff_eq_eval_mul_sqrt_det`](../src/LeanPaper/ImportedSection56/FiniteDeterminant.lean)

## Literal corrections and retained limits

- **3.4:** The audited actual-family k=2, m=1, N=1, K=6 first minor is positive constant. Degree and root count now equal direction rank, but the literal universal r-root list remains false. Interlacing and all-rank Dodgson assembly remain separate.
- **3.5:** `I+tB` requires `1+t*a_i` and `t^2*b_i^2`; normalized and original determinant ratios also require their Gram factors. The new numerical diagnostic is a general matrix calculation, not an asserted manuscript-family counterexample.
- **3.6:** Fixed-K strict Hankel positivity stops at distinct inverse-square support size. At order h+1 the actual determinant is zero. The corrected bound is `h^(-1/(2r)) <= S_(2r)^(-1/(2r))/d_min <= 1`. With the printed prefactor odd logarithmic derivatives use `(q-r)^(-m)`. Corrected convergence and first/second derivative formulas do not certify the false original or all higher moments.
- **3.7:** All-derivative Turan and weak normalized Newton are now proved. Strict strengthened/normalized Newton clauses and actual coefficient nonvanishing remain open. Generic distinctness prose is not a witness.
- **4.4 / 4.6:** Keep paper constants 11.411, 0.23310 and 3.73980 distinct from historical 11.407/10.954, 0.23338 and 3.73872. No unconditional odd-zeta irrationality, effective measure or RH conclusion is inferred.

## Proposed ledger reconciliation

The coordinated JSON/CSV ledger update retains all original 45 IDs/titles/order and legacy fields. It marks 3.1 and 4.3 as complete semantic coverage and updates the proved components for 2.2/2.3, 3.4, 3.6 and 3.7 without closing their listed gaps. Keep 2.4/2.5 functional-basis identification open and preserve the false literal statements separately from corrections. The expanded final global audit passed; native Windows remains separate.

Evidence: [current acceptance receipt](../validation/linux/acceptance.json), [prior intake scope](THEOREM_REBUILD_INTAKE.md), [manuscript issues](manuscript_issues.txt), and the original supplied 52-page manuscript.
