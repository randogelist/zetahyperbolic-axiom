import Definition_2_1_Order_s_Rational_Moment_Functional
import Theorem_2_4_Canonical_Basis_Invariance
import Theorem_2_5_Lagrange_Pole_Diagonalization
import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk
import Theorem_3_1_General_Odd_Weight_Endpoint
import Theorem_3_1_Positive_Moment_Realization
import Theorem_4_1_Spectral_Irrationality_Measure_Criterion
import MAIN_CHAIN
import Theorem_3_1_Hyperbolic_Weight
import Theorem_3_1_Hyperbolic_Moments
import Zetahyperbolic.CoreLinearAlgebra
import Zetahyperbolic.Foundations
import Zetahyperbolic.Section3Elementary
import Zetahyperbolic.Section2Checked
import Zetahyperbolic.ManuscriptCompatibility
import Theorem_3_1_Concrete_Moment_Realization
import Theorem_3_1_Rational_Integral_Bridge
import ANALYTIC_FRONTIER
import Zetahyperbolic.MainChain
import Zetahyperbolic.AnalyticMainChain
import Theorem_3_1_Pole_Scaling
import Theorem_3_1_Coth_Partial_Fractions
import Theorem_3_1_Zeta_Tail
import Theorem_3_1_Bose_Tail_Integral
import Theorem_3_1_Pole_Integral_Identity
import MAIN_CHAIN_ASSEMBLED
import Theorem_4_1_General_Odd_Zeta_Application
import Theorem_4_1_Integer_Polynomial_Irrationality
import Theorem_4_1_Linear_Odd_Zeta_Family
import MAIN_CHAIN_ARITHMETIC
import Theorem_4_1_Direct_Irrationality_From_Decay
import Theorem_2_4_Primitive_Normalization_Minimality
import MAIN_CHAIN_IRRATIONALITY
import Theorem_2_5_Weight_Change
import Theorem_4_1_Leading_Coefficient_Gap
import PAPER_PROVEN_CORE
import PAPER_02_03_UNCONDITIONAL
import Paper.Definition_2_1
import Paper.Lemma_2_2
import Paper.Lemma_2_3
import Paper.Theorem_2_4
import Paper.Theorem_2_5
import Paper.Theorem_3_1
import Paper.Proposition_3_2
import Paper.Theorem_3_3
import Paper.Theorem_3_4
import Paper.Corollary_3_5
import Paper.Corollary_3_6
import PaperChain.Stage01
import PaperChain.Stage02
import PaperChain.Stage03
import PaperChain.Stage04
import PaperChain.Stage05
import PaperChain.Stage06
import PaperChain.Stage07
import PaperChain.Stage08
import PaperChain.Stage09
import PaperChain.Stage10
import PaperChain.Audit
import PaperChain.Stage03UnconditionalBridge
import PaperChain.Stage03UnconditionalAudit
import PaperChain.Stage04PrincipalMinorCenter
import Theorem_4_1_Determinant_Log_Energy
import Theorem_4_1_Content_Gram_Cancellation
import Theorem_4_1_Adjacent_Log_Increment
import Theorem_4_1_Pole_Log_Slope
import PaperChain.Stage05PrimitiveBridge
import PaperChain.Stage05RateGapBridge
import PaperChain.Stage08FinitePotentialBridge
import PaperChain.Stage08PoleProductBridge
import PaperChain.Stage05ContentGramBridge
import PaperChain.Stage05AdjacentDriftBridge
import PaperChain.Stage05AdjacentDriftAudit
import PaperChain.Stage05ContentGramAudit
import PaperChain.Stage05PrimitiveAudit
import PaperChain.Stage07WeightShiftBridge
import PaperChain.Stage05RateGapAudit
import PaperChain.Stage08FinitePotentialAudit
import PaperChain.Stage08PoleProductAudit
import ProofAdvances.Theorem_3_4
import ProofAdvances.Corollary_3_6
import ProofAdvances.Corollary_3_6_FullGram
import ProofAdvances.Corollary_3_6_WeightedCorrected
import ProofAdvances.Corollary_3_6_ExactFiniteRank
import ProofAdvances.Corollary_3_6_AllPrincipalMinors
import LeanPaper.PullbackReflection
import LeanPaper.SingularSlope
import LeanPaper.PrincipalMinorRealRoots
import LeanPaper.ReciprocalRootMoments
import LeanPaper.SingularPrincipalMinorExample
import LeanPaper.AxiomWalk
import LeanPaper.Rebuild.PartialFractionsCore
import LeanPaper.Rebuild.PartialFractionsQuotient
import LeanPaper.Rebuild.PartialFractionsResidues
import LeanPaper.RebuildKernelBridge
import LeanPaper.ImportedCharacter.ShiftedPole
import LeanPaper.ImportedMultiweight.PositiveSlopeSpectrum
import LeanPaper.ImportedSection3.CubicNewton
import LeanPaper.ImportedSection3.CubicTuran
import LeanPaper.ImportedSection3.NormalizedContinuedFraction
import LeanPaper.ImportedSection3.PowerSumExtrema
import LeanPaper.ImportedSection3.RealExponent
import LeanPaper.ImportedSection4.Proposition_4_2_Resultant_Product_Barrier
import LeanPaper.ImportedSection4.Proposition_4_3_PadicDisk
import LeanPaper.ImportedSection56.DualMoments
import LeanPaper.ImportedSection56.FiniteDeterminant
import LeanPaper.ImportedSection56.TriplePoleHermite
import LeanPaper.Section2FiniteDifference
import LeanPaper.Section2LagrangeBasis
import LeanPaper.Section6BetaFinite
import LeanPaper.ImportedCharacter.CharacterPositive
import LeanPaper.ImportedSection3.AllDegreeTuran
import LeanPaper.ImportedSection3.PoleKernel
import LeanPaper.ImportedSection3.RootMomentBounds
import LeanPaper.ImportedSection3.SignStructure
import LeanPaper.ImportedSection4.Proposition_4_3_IsometricExtension
import LeanPaper.ImportedSection4.Theorem_4_6_Leading_Coefficient_Determinant_Barrier
import LeanPaper.ImportedSection56.DualAffineAlgebra
import LeanPaper.Section2LagrangeBridge
import LeanPaper.ImportedCharacter.PositiveSlope
import LeanPaper.ImportedSection3.SlopeSign
import LeanPaper.ImportedSection3.StrictTuranRolle
import LeanPaper.ImportedSection4.Proposition_4_3_ComplexPadicDisk
import LeanPaper.ImportedSection4.Theorem_4_7_Finite_Root_Cluster_Count
import LeanPaper.ImportedSection56.DualPencilCCT
import LeanPaper.ImportedSection56.KreinIdentity
import LeanPaper.Section2LagrangeIdentification
import LeanPaper.ImportedMultiweight.FiniteMultiweightCone
import LeanPaper.ImportedSection3.ActualPoleKernel
import LeanPaper.ImportedSection4.Proposition_4_8_Factor_Distance_Bounds
import LeanPaper.ImportedSection56.CoefficientGram
import LeanPaper.ImportedSection56.DualDiscriminant
import LeanPaper.ImportedSection56.DualTopCoefficient
import LeanPaper.ImportedSection56.RankOneWitness
import LeanPaper.Section4ManuscriptBridge
import LeanPaper.ImportedMultiweight.AnchoredSemidefiniteCone
import LeanPaper.ImportedSection3.Jacobi
import LeanPaper.ImportedSection56.DualQuadraticRoot
import LeanPaper.ImportedSection56.DualSOS
import LeanPaper.ImportedSection56.DualStrictDiscriminant
import LeanPaper.ImportedSection56.DualWeightInvariance
import LeanPaper.ImportedSection56.FiniteKreinCone
import LeanPaper.ImportedSection56.PositiveSlopeSpectrum
import LeanPaper.ImportedSection56.ZetaSevenBound
import LeanPaper.ImportedSection3.ExactTaylor
import LeanPaper.ImportedSection56.DualBasisCongruence
import LeanPaper.ImportedSection56.DualRowSeparation
import LeanPaper.ImportedSection56.FullMonomial
import LeanPaper.ImportedSection56.DualNonsingularDegree
import LeanPaper.ImportedSection56.DualNullspace
import LeanPaper.ImportedSection56.SelectedMonomial
import LeanPaper.ImportedSection56.UnimodularMonomial
import LeanPaper.Section5DualSpectrum
import Lean

/-! Every active project declaration is independently traversed for forbidden axioms.
Exact Lean statements and explicit hypotheses are certified; full manuscript equivalence is separate. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean
#check ManuscriptChain.MAIN_CHAIN_UNCONDITIONAL
#check Zetahyperbolic.ORIGINAL_EXACT_ZERO_FREE_DISK
#check ManuscriptChain.PrincipalMinors.determinant_center_pos
#check ManuscriptChain.PrincipalMinors.determinant_ne_zero
#check ManuscriptChain.PrincipalMinors.leading_determinant_center_pos
#check ManuscriptChain.PrincipalMinors.two_index_strict
#check PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_posSemidef
#check PaperAdvances.Corollary3_6_WeightedCorrected.weighted_hankel_det_zero_above_support
#check PaperAdvances.Corollary3_6_ExactFiniteRank.weighted_det_pos_iff_order_le_support
#check PaperAdvances.Corollary3_6_AllPrincipalMinors.weighted_all_principal_minors_positive
#check LeanPaper.PullbackReflection.rationalValue_pullback
#check LeanPaper.PullbackReflection.muFunctionalPoly_eq_pulledMoment
#check LeanPaper.PullbackReflection.finite_span_reflection
#check LeanPaper.PullbackReflection.finite_pole_difference
#check LeanPaper.SingularSlope.all_complex_roots_real_even_if_slope_singular
#check LeanPaper.PrincipalMinorRealRoots.original_principal_zeros_real
#check LeanPaper.PrincipalMinorRealRoots.original_leading_principal_zeros_real
#check LeanPaper.ReciprocalRootMoments.manuscript_reciprocal_moments
#check LeanPaper.ReciprocalRootMoments.reciprocalHankel_det_pos_iff
#check LeanPaper.ReciprocalRootMoments.reciprocalHankel_det_zero_above_distinct_support
#check LeanPaper.SingularPrincipalMinorExample.first_slope_zero
#check LeanPaper.SingularPrincipalMinorExample.first_minor_no_real_zero
#check LeanPaper.SingularPrincipalMinorExample.first_minor_natDegree_zero
#check ManuscriptChain.PartialFractions.data_quotient_eq_actual
#check ManuscriptChain.PartialFractions.residueCoeff_eq_actual
#check ManuscriptChain.PartialFractions.rational_kernel_decomposition
#check LeanPaper.RebuildKernelBridge.resolvedKernel_eq_fraction_all_real
#check LeanPaper.RebuildKernelBridge.gram_eq_fraction_integral
#check PaperOrder.CoreAlgebra.dualConstant_swap
#check PaperOrder.CoreAlgebra.dualEntry_derivative
#check PaperOrder.CoreAlgebra.dualSlopeMatrix_symmetric
#check PaperOrder.CoreAlgebra.dualSlopeMatrix_eq_CCT
#check PaperOrder.CoreAlgebra.dualPencil_decomposition
#check PaperOrder.CoreAlgebra.dualConstantMatrix_symmetric
#check PaperOrder.PrincipalTheorems.coefficientSlope_quadratic_sos
#check PaperOrder.PrincipalTheorems.coefficientSlope_posDef
#check PaperOrder.PrincipalTheorems.positiveSlopePencil_factorization_exists
#check PaperOrder.PrincipalTheorems.positiveSlopePencil_degree
#check PaperOrder.PrincipalTheorems.positiveSlopePencil_every_complex_root_real
#check PaperOrder.PrincipalTheorems.independent_coefficients_full_hyperbolicity
#check PaperOrder.CoreAlgebra.dualDelta_coefficient_dimension
#check PaperOrder.CoreAlgebra.dualDelta_natDegree_le
#check PaperOrder.CoreAlgebra.dualSlopeQuadraticForm_sos
#check PaperOrder.CoreAlgebra.dualSlopeQuadraticForm_nonneg
#check PaperOrder.CoreAlgebra.dualCoefficientRowsSeparate_exists_nonzero
#check PaperOrder.CoreAlgebra.dualSlopeQuadraticForm_pos_of_separation
#check PaperOrder.CoreAlgebra.dualSlopeQuadraticForm_zero_iff
#check PaperOrder.CoreAlgebra.dualSlopeQuadraticForm_pos_iff_rowsSeparate
#check PaperOrder.CoreAlgebra.dualEntry_derivative_weight_independent
#check PaperOrder.CoreAlgebra.dualDelta_top_coefficient_weight_independent
#check PaperOrder.CoreAlgebra.dualSlopeMatrix_rowChange
#check PaperOrder.CoreAlgebra.dualDelta_top_coeff_rowChange
#check PaperOrder.CoreAlgebra.dualDelta_degree_rowChange
#check PaperOrder.CoreAlgebra.dualDelta_degree_of_nonsingular_slope
#check PaperOrder.CoreAlgebra.dualDelta_topCoeff_nonzero_rowChange_iff
#check PaperOrder.CoreAlgebra.dualDelta_degree_rowChange_of_nonsingular_slope
#check PaperOrder.CoreAlgebra.dualFullMonomialSlope_one
#check PaperOrder.CoreAlgebra.dualFullMonomialDelta_degree
#check PaperOrder.CoreAlgebra.dualSelectedMonomialSlope_one
#check PaperOrder.CoreAlgebra.dualSelectedMonomialDelta_degree
#check PaperOrder.CoreAlgebra.dualUnimodularSelectedMonomial_top_coeff
#check PaperOrder.CoreAlgebra.dualUnimodularSelectedMonomial_degree
#check PaperOrder.CoreAlgebra.dualTwoByTwo_det_expansion
#check PaperOrder.CoreAlgebra.dualTwoByTwo_discriminant_sos
#check PaperOrder.CoreAlgebra.dualTwoByTwo_discriminant_nonneg
#check PaperOrder.CoreAlgebra.dualTwoByTwo_discriminant_pos_of_nonproportional
#check PaperOrder.CoreAlgebra.realQuadratic_has_root_of_discriminant_nonneg
#check PaperOrder.CoreAlgebra.dualTwoByTwo_det_has_real_zero
#check PaperOrder.PrincipalTheorems.weightSeven_binomial
#check PaperOrder.PrincipalTheorems.weightSeven_Krein_bilinear
#check PaperOrder.PrincipalTheorems.weightSeven_Krein_quadratic
#check PaperOrder.PrincipalTheorems.weightSeven_Krein_infinite_modes
#check PaperOrder.PrincipalTheorems.finiteKreinGram_posDef
#check PaperOrder.PrincipalTheorems.finiteKreinGram_neg_posDef
#check PaperOrder.PrincipalTheorems.negativeWeightSeven_actual_pencil
#check PaperOrder.PrincipalTheorems.negativeWeightSeven_rational_root
#check PaperOrder.PrincipalTheorems.negativeWeightSeven_below_zero_at_zeta
#check PaperOrder.PrincipalTheorems.positiveWeightSeven_at_zeta
#check PaperOrder.PrincipalTheorems.zetaSeven_tail_le_one_div_64
#check PaperOrder.PrincipalTheorems.zetaSeven_lt_38_div_37
#check PaperOrder.PrincipalTheorems.weightSeven_rankOne_negative_unconditional
#check Zetahyperbolic.TriplePoleRepair.hermite_congruence
#check Zetahyperbolic.TriplePoleRepair.momentMatrix_det_ne_zero
#check Zetahyperbolic.Theorem6_10.abs_top_coefficient_eq_eval_mul_relative_det
#check Zetahyperbolic.Theorem6_10.abs_top_coefficient_eq_eval_mul_spectral_det
#check Zetahyperbolic.Theorem6_10.abs_top_coefficient_eq_eval_mul_sqrt_det
#check Zetahyperbolic.Theorem6_10.abs_leadingCoeff_eq_eval_mul_sqrt_det
#check PaperChronology.Paper10.PAPER10_BETA_VANDERMONDE_RESIDUAL_SIGN
#check PaperChronology.Paper10.PAPER10_BETA_VANDERMONDE_EVEN_BASE
#check PaperChronology.Paper10.PAPER10_BETA_VANDERMONDE_ODD_BASE
#check PaperChronology.Paper10.PAPER10_BETA_FULL_CHARACTER_VANDERMONDE_CANCELLATION
#check PaperChronology.Paper10.PAPER10_POSITIVE_DIAGONAL_NONNEG
#check PaperChronology.Paper10.PAPER10_POSITIVE_DIAGONAL_STRICT
#check PaperChronology.Paper10.PAPER10_TWO_NODE_VANDERMONDE_ZERO
#check PaperChronology.Paper10.PAPER10_TWO_NODE_VANDERMONDE_GRAM_STRICT
#check PaperChronology.Paper10.PAPER10_FINITE_WEIGHTED_GRAM_STRICT
#check PaperChronology.Paper10.PAPER10_BILINEAR_TENSOR_GRID_ZERO
#check PaperChronology.Paper10.PAPER10_BILINEAR_TENSOR_GRID_GRAM_STRICT
#check PaperChronology.Paper10.PAPER10_BETA_REAL_SIGN_NORMALIZATION
#check PaperChronology.Paper10.PAPER10_BETA_NORMALIZED_RESIDUE_EQ
#check PaperChronology.Paper10.PAPER10_BETA_NORMALIZED_RESIDUES_POSITIVE
#check PaperChronology.Paper10.PAPER10_BETA_INJECTIVE_PENCIL_STRICT
#check PaperChronology.Paper10.PAPER10_BETA_TWO_NODE_PENCIL_STRICT
#check PaperChronology.Paper10.PAPER10_BETA_BILINEAR_TENSOR_GRID_STRICT
#check PaperChronology.Paper10.PAPER10_TWO_NODE_GRAM_DETERMINANT
#check PaperChronology.Paper10.PAPER10_TWO_NODE_GRAM_DETERMINANT_POSITIVE
#check PaperChronology.Paper10.PAPER10_THREE_NODE_VANDERMONDE_ZERO
#check PaperChronology.Paper10.PAPER10_THREE_NODE_WEIGHTED_GRAM_STRICT
#check PaperChronology.Paper10.PAPER10_BETA_THREE_NODE_PENCIL_STRICT
#check PaperChronology.Paper10.PAPER10_DIFFERENTIAL_SHIFT_POLE_ALIGNMENT
#check PaperChronology.Paper10.PAPER10_DIFFERENTIAL_SHIFT_FINITE_COUPLING
#check LeanPaper.Section5DualSpectrum.actual_dual_degree
#check LeanPaper.Section5DualSpectrum.actual_dual_zeros_real
#check LeanPaper.Section5DualSpectrum.selected_monomial_dual_zeros_real
#check PaperAdvances.Theorem3_9_ShiftedPole.hurwitz_slope_nonsingular
#check PaperAdvances.Theorem3_9_ShiftedPole.hurwitz_complex_roots_real
#check PaperAdvances.Theorem3_9_CharacterPositive.all_fekete_laplace_numerators_pos
#check PaperAdvances.Theorem3_9_CharacterPositive.all_rational_character_kernels_pos
#check PaperAdvances.Theorem3_9_PositiveSlope.poleM_posDef
#check PaperAdvances.Theorem3_9_PositiveSlope.shiftedSlope_posDef
#check PaperAdvances.Theorem5_2_RealRoots.positive_slope_factorization
#check PaperAdvances.Theorem5_2_RealRoots.positive_slope_exact_degree
#check PaperAdvances.Theorem5_2_RealRoots.positive_slope_complex_roots_real
#check PaperAdvances.Theorem6_6_FiniteMultiweightCone.FINITE_MULTIWEIGHT_SPECTRAL_HYPERBOLICITY
#check PaperAdvances.Theorem6_6_FiniteMultiweightCone.FINITE_MULTIWEIGHT_STRICT_TURAN
#check PaperAdvances.Theorem6_6_AnchoredSemidefiniteCone.ANCHORED_FINITE_CONE_POSDEF
#check PaperAdvances.Theorem6_6_AnchoredSemidefiniteCone.ANCHORED_FINITE_CONE_SPECTRAL_PACKAGE
#check PaperAdvances.Theorem3_9_CharacterPositive.all_fekete_numerators_pos
#check PaperAdvances.Theorem3_9_CharacterPositive.alternating_character_vandermonde_cancellation
#check PaperAdvances.Theorem3_9_ShiftedPole.poleM_det_ne_zero
#check PaperAdvances.Theorem3_9_ShiftedPole.polePencil_complex_roots_real
#check PaperAdvances.Theorem6_6_FiniteMultiweightCone.FINITE_MULTIWEIGHT_POSITIVE_DIRECTION
#check PaperAdvances.Theorem5_2_RealRoots.det_add_scalar_of_hermitian
#check PaperAdvances.Theorem3_8_Actual.actual_derivative_eq_real_slope
#check PaperAdvances.Theorem3_8_Actual.actual_relative_charpoly_eq_pole
#check PaperAdvances.Theorem3_8_Actual.actual_relative_trace_eq_pole
#check PaperAdvances.Theorem3_7_AllDegrees.turan_mul_linear
#check PaperAdvances.Theorem3_7_AllDegrees.finite_affine_turan_nonnegative
#check PaperAdvances.Theorem3_7_AllDegrees.THEOREM_3_7_ACTUAL_ALL_DEGREES
#check LeanPaper.Section3Newton.cubic_newton_first
#check LeanPaper.Section3Newton.cubic_newton_second
#check PaperAdvances.Theorem3_7.cubic_first_turan_nonnegative
#check PaperAdvances.Theorem3_7.cubic_second_turan_nonnegative
#check PaperAdvances.Theorem3_7.three_mode_taylor_bound
#check PaperAdvances.Theorem3_8_ExactTaylor.unit_det_linear_coeff
#check PaperAdvances.Theorem3_8_ExactTaylor.affine_det_exact_second_order
#check PaperAdvances.Theorem3_8_Jacobi.unitDetPoly_derivative
#check PaperAdvances.Theorem3_8_Jacobi.unitDetPoly_eval
#check PaperAdvances.Theorem3_8_Jacobi.unitDet_hasDerivAt
#check PaperAdvances.Theorem3_8_Jacobi.affineDet_factor_pointwise
#check PaperAdvances.Theorem3_8_Jacobi.affineDet_hasDerivAt
#check PaperAdvances.Theorem3_8_Jacobi.affineDet_log_hasDerivAt
#check PaperAdvances.Theorem3_8_Jacobi.actual_affine_log_jacobi
#check LeanPaper.Section3ContinuedFractions.corollary_3_5_normalized_two_det
#check LeanPaper.Section3ContinuedFractions.corollary_3_5_two_level_schur_identity
#check LeanPaper.Section3ContinuedFractions.normalized_three_continuant_recurrence
#check LeanPaper.Section3ContinuedFractions.normalized_three_schur_identity
#check LeanPaper.Section3ContinuedFractions.normalized_three_continuant_eq_det
#check PaperAdvances.Theorem3_8_Kernel.charpoly_relative_eq_pole
#check PaperAdvances.Theorem3_8_Kernel.trace_relative_eq_pole
#check PaperAdvances.Theorem3_8_Kernel.kernelMatrix_entry
#check PaperAdvances.Corollary3_6_PowerSumExtrema.positive_atomic_moment_bounds
#check PaperAdvances.Corollary3_6_PowerSumExtrema.even_atomic_moment_bounds
#check PaperAdvances.Proposition3_2.slope_det_ne_zero
#check PaperAdvances.Proposition3_2.all_complex_roots_real
#check LeanPaper.Section3RootMomentBounds.actual_reciprocal_moment_bounds
#check PaperAdvances.Theorem3_3.actual_gram_det_pos
#check PaperAdvances.Theorem3_3.leading_coefficient_product
#check PaperAdvances.Theorem3_3.positive_pole_count_constant
#check PaperAdvances.Theorem3_3_Sign.slope_det_pos_iff
#check PaperAdvances.Theorem3_3_Sign.slope_det_neg_iff
#check PaperAdvances.Theorem3_7_StrictRolle.finite_affine_turan_strict_offroots
#check PaperAdvances.Theorem3_7_StrictRolle.THEOREM_3_7_ACTUAL_TURAN_STRICT
#check PaperAdvances.Theorem3_7_StrictRolle.THEOREM_3_7_ACTUAL_TURAN_EQUALITY
#check PaperAdvances.Theorem3_7_StrictRolle.THEOREM_3_7_ACTUAL_CRITICAL_POINT_SEPARATION
#check PaperOrder.Section4.proposition_4_2_resultant_product_barrier
#check PaperAdvances.Proposition4_3_ComplexPadicDisk.PROPOSITION_4_3_INTEGRAL_COMPLEX_PADIC
#check PaperAdvances.Proposition4_3_ComplexPadicDisk.PROPOSITION_4_3_INTEGER_COMPLEX_PADIC
#check PaperAdvances.Proposition4_3_IsometricExtension.ISOMETRIC_EXTENSION_UNIT_DISK
#check PaperAdvances.Proposition4_3_IsometricExtension.PROPOSITION_4_3_INTEGRAL_ISOMETRIC_EXTENSION
#check PaperAdvances.Proposition4_3_PadicDisk.finite_ultrametric_sum_strict
#check PaperAdvances.Proposition4_3_PadicDisk.ultrametric_eval_norm_eq_constant
#check PaperAdvances.Proposition4_3_PadicDisk.ultrametric_unit_coeff_disk
#check PaperAdvances.Proposition4_3_PadicDisk.PROPOSITION_4_3_INTEGRAL_QPADIC
#check PaperAdvances.Proposition4_3_PadicDisk.PROPOSITION_4_3_INTEGER_QPADIC
#check PaperOrder.Section4.proposition_4_8_distance_product_nonnegative
#check PaperOrder.Section4.proposition_4_8_distance_product_lower
#check PaperOrder.Section4.proposition_4_8_distance_product_upper
#check PaperOrder.Section4.proposition_4_8_factor_evaluation_bounds
#check PaperOrder.Section4.theorem_4_6_integer_leading_coefficient_barrier
#check PaperOrder.Section4.theorem_4_6_integer_evaluation_lower_bound
#check PaperOrder.Section4.theorem_4_6_reciprocal_evaluation_lower_bound
#check PaperOrder.Section4.theorem_4_7_finite_cluster_sum_bound
#check PaperOrder.Section4.theorem_4_7_cluster_fraction_lower_bound
#check PaperOrder.Section4.theorem_4_7_cluster_percentage_arithmetic
#check LeanPaper.Section2FiniteDifference.tau_monomial_difference
#check LeanPaper.Section2FiniteDifference.finite_span_difference
#check LeanPaper.Section2FiniteDifference.finite_span_difference_coefficient
#check LeanPaper.Section2FiniteDifference.finite_span_translation
#check LeanPaper.Section2FiniteDifference.function_and_moment_difference
#check Zetahyperbolic.lagrangePolePolynomial_eval_self
#check Zetahyperbolic.lagrangePolePolynomial_eval_ne
#check Zetahyperbolic.lagrangePolePolynomial_eval
#check Zetahyperbolic.lagrangePolePolynomial_eval_eq_one_iff
#check Zetahyperbolic.lagrangePoleEvaluationMatrix_eq_one
#check Zetahyperbolic.det_lagrangePoleEvaluationMatrix
#check Zetahyperbolic.lagrangePoleEvaluationMatrix_det_ne_zero
#check Zetahyperbolic.lagrangePoleEvaluationMatrix_mulVec
#check LeanPaper.Section2LagrangeBridge.polePolynomial_eval
#check LeanPaper.Section2LagrangeBridge.polePolynomial_natDegree
#check LeanPaper.Section2LagrangeBridge.polePolynomial_ne_zero
#check LeanPaper.Section2LagrangeBridge.polePolynomial_eval_sum
#check LeanPaper.Section2LagrangeBridge.coefficientMatrix_mul_vandermonde
#check LeanPaper.Section2LagrangeBridge.coefficientMatrix_eq_inverse
#check LeanPaper.Section2LagrangeBridge.coefficientMatrix_det_ne_zero
#check LeanPaper.Section2LagrangeBridge.lagrange_pencil_eq_actual
#check LeanPaper.Section2LagrangeBridge.actual_lagrange_entries
#check LeanPaper.Section2LagrangeBridge.actual_lagrange_slope
#check LeanPaper.Section2LagrangeIdentification.negative_square_injective
#check LeanPaper.Section2LagrangeIdentification.archive_polynomial_eq_mathlib
#check LeanPaper.Section2LagrangeIdentification.archive_polynomial_natDegree
#check LeanPaper.Section2LagrangeIdentification.archive_polynomial_eval
#check LeanPaper.Section2LagrangeIdentification.archive_polynomial_eq_constructed
#check LeanPaper.Section2LagrangeIdentification.archive_coefficients_eq_inverse
#check LeanPaper.Section4ManuscriptBridge.primitive_leading_barrier_identity
#check LeanPaper.Section4ManuscriptBridge.primitive_evaluation_lower_of_inverse_ratio_bound
#check LeanPaper.Section4ManuscriptBridge.manuscript_spectral_cluster_fraction
#check LeanPaper.Section4ManuscriptBridge.manuscript_large_exponent_gives_close_root
#check LeanPaper.Section4ManuscriptBridge.manuscript_primitive_complex_padic_disk
#check LeanPaper.Section5DualSpectrum.actualDualPencil_polynomialMatrix
#check LeanPaper.Section5DualSpectrum.actualDualPencil_detPolynomial
#check LeanPaper.Section5DualSpectrum.selected_monomial_rows_separate
run_cmd Elab.Command.liftCoreM do
  let env := (← getEnv).setExporting false
  let allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let projectModules : Array Name := #[
    `Definition_2_1_Order_s_Rational_Moment_Functional,
    `Theorem_2_4_Canonical_Basis_Invariance,
    `Theorem_2_5_Lagrange_Pole_Diagonalization,
    `Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk,
    `Theorem_3_1_General_Odd_Weight_Endpoint,
    `Theorem_3_1_Positive_Moment_Realization,
    `Theorem_4_1_Spectral_Irrationality_Measure_Criterion,
    `MAIN_CHAIN,
    `Theorem_3_1_Hyperbolic_Weight,
    `Theorem_3_1_Hyperbolic_Moments,
    `Zetahyperbolic.CoreLinearAlgebra,
    `Zetahyperbolic.Foundations,
    `Zetahyperbolic.Section3Elementary,
    `Zetahyperbolic.Section2Checked,
    `Zetahyperbolic.ManuscriptCompatibility,
    `Theorem_3_1_Concrete_Moment_Realization,
    `Theorem_3_1_Rational_Integral_Bridge,
    `ANALYTIC_FRONTIER,
    `Zetahyperbolic.MainChain,
    `Zetahyperbolic.AnalyticMainChain,
    `Theorem_3_1_Pole_Scaling,
    `Theorem_3_1_Coth_Partial_Fractions,
    `Theorem_3_1_Zeta_Tail,
    `Theorem_3_1_Bose_Tail_Integral,
    `Theorem_3_1_Pole_Integral_Identity,
    `MAIN_CHAIN_ASSEMBLED,
    `Theorem_4_1_General_Odd_Zeta_Application,
    `Theorem_4_1_Integer_Polynomial_Irrationality,
    `Theorem_4_1_Linear_Odd_Zeta_Family,
    `MAIN_CHAIN_ARITHMETIC,
    `Theorem_4_1_Direct_Irrationality_From_Decay,
    `Theorem_2_4_Primitive_Normalization_Minimality,
    `MAIN_CHAIN_IRRATIONALITY,
    `Theorem_2_5_Weight_Change,
    `Theorem_4_1_Leading_Coefficient_Gap,
    `PAPER_PROVEN_CORE,
    `PAPER_02_03_UNCONDITIONAL,
    `Paper.Definition_2_1,
    `Paper.Lemma_2_2,
    `Paper.Lemma_2_3,
    `Paper.Theorem_2_4,
    `Paper.Theorem_2_5,
    `Paper.Theorem_3_1,
    `Paper.Proposition_3_2,
    `Paper.Theorem_3_3,
    `Paper.Theorem_3_4,
    `Paper.Corollary_3_5,
    `Paper.Corollary_3_6,
    `PaperChain.Stage01,
    `PaperChain.Stage02,
    `PaperChain.Stage03,
    `PaperChain.Stage04,
    `PaperChain.Stage05,
    `PaperChain.Stage06,
    `PaperChain.Stage07,
    `PaperChain.Stage08,
    `PaperChain.Stage09,
    `PaperChain.Stage10,
    `PaperChain.Audit,
    `PaperChain.Stage03UnconditionalBridge,
    `PaperChain.Stage03UnconditionalAudit,
    `PaperChain.Stage04PrincipalMinorCenter,
    `Theorem_4_1_Determinant_Log_Energy,
    `Theorem_4_1_Content_Gram_Cancellation,
    `Theorem_4_1_Adjacent_Log_Increment,
    `Theorem_4_1_Pole_Log_Slope,
    `PaperChain.Stage05PrimitiveBridge,
    `PaperChain.Stage05RateGapBridge,
    `PaperChain.Stage08FinitePotentialBridge,
    `PaperChain.Stage08PoleProductBridge,
    `PaperChain.Stage05ContentGramBridge,
    `PaperChain.Stage05AdjacentDriftBridge,
    `PaperChain.Stage05AdjacentDriftAudit,
    `PaperChain.Stage05ContentGramAudit,
    `PaperChain.Stage05PrimitiveAudit,
    `PaperChain.Stage07WeightShiftBridge,
    `PaperChain.Stage05RateGapAudit,
    `PaperChain.Stage08FinitePotentialAudit,
    `PaperChain.Stage08PoleProductAudit,
    `ProofAdvances.Theorem_3_4,
    `ProofAdvances.Corollary_3_6,
    `ProofAdvances.Corollary_3_6_FullGram,
    `ProofAdvances.Corollary_3_6_WeightedCorrected,
    `ProofAdvances.Corollary_3_6_ExactFiniteRank,
    `ProofAdvances.Corollary_3_6_AllPrincipalMinors,
    `LeanPaper.PullbackReflection,
    `LeanPaper.SingularSlope,
    `LeanPaper.PrincipalMinorRealRoots,
    `LeanPaper.ReciprocalRootMoments,
    `LeanPaper.SingularPrincipalMinorExample,
    `LeanPaper.AxiomWalk,
    `LeanPaper.Rebuild.PartialFractionsCore,
    `LeanPaper.Rebuild.PartialFractionsQuotient,
    `LeanPaper.Rebuild.PartialFractionsResidues,
    `LeanPaper.RebuildKernelBridge,
    `LeanPaper.ImportedCharacter.ShiftedPole,
    `LeanPaper.ImportedMultiweight.PositiveSlopeSpectrum,
    `LeanPaper.ImportedSection3.CubicNewton,
    `LeanPaper.ImportedSection3.CubicTuran,
    `LeanPaper.ImportedSection3.NormalizedContinuedFraction,
    `LeanPaper.ImportedSection3.PowerSumExtrema,
    `LeanPaper.ImportedSection3.RealExponent,
    `LeanPaper.ImportedSection4.Proposition_4_2_Resultant_Product_Barrier,
    `LeanPaper.ImportedSection4.Proposition_4_3_PadicDisk,
    `LeanPaper.ImportedSection56.DualMoments,
    `LeanPaper.ImportedSection56.FiniteDeterminant,
    `LeanPaper.ImportedSection56.TriplePoleHermite,
    `LeanPaper.Section2FiniteDifference,
    `LeanPaper.Section2LagrangeBasis,
    `LeanPaper.Section6BetaFinite,
    `LeanPaper.ImportedCharacter.CharacterPositive,
    `LeanPaper.ImportedSection3.AllDegreeTuran,
    `LeanPaper.ImportedSection3.PoleKernel,
    `LeanPaper.ImportedSection3.RootMomentBounds,
    `LeanPaper.ImportedSection3.SignStructure,
    `LeanPaper.ImportedSection4.Proposition_4_3_IsometricExtension,
    `LeanPaper.ImportedSection4.Theorem_4_6_Leading_Coefficient_Determinant_Barrier,
    `LeanPaper.ImportedSection56.DualAffineAlgebra,
    `LeanPaper.Section2LagrangeBridge,
    `LeanPaper.ImportedCharacter.PositiveSlope,
    `LeanPaper.ImportedSection3.SlopeSign,
    `LeanPaper.ImportedSection3.StrictTuranRolle,
    `LeanPaper.ImportedSection4.Proposition_4_3_ComplexPadicDisk,
    `LeanPaper.ImportedSection4.Theorem_4_7_Finite_Root_Cluster_Count,
    `LeanPaper.ImportedSection56.DualPencilCCT,
    `LeanPaper.ImportedSection56.KreinIdentity,
    `LeanPaper.Section2LagrangeIdentification,
    `LeanPaper.ImportedMultiweight.FiniteMultiweightCone,
    `LeanPaper.ImportedSection3.ActualPoleKernel,
    `LeanPaper.ImportedSection4.Proposition_4_8_Factor_Distance_Bounds,
    `LeanPaper.ImportedSection56.CoefficientGram,
    `LeanPaper.ImportedSection56.DualDiscriminant,
    `LeanPaper.ImportedSection56.DualTopCoefficient,
    `LeanPaper.ImportedSection56.RankOneWitness,
    `LeanPaper.Section4ManuscriptBridge,
    `LeanPaper.ImportedMultiweight.AnchoredSemidefiniteCone,
    `LeanPaper.ImportedSection3.Jacobi,
    `LeanPaper.ImportedSection56.DualQuadraticRoot,
    `LeanPaper.ImportedSection56.DualSOS,
    `LeanPaper.ImportedSection56.DualStrictDiscriminant,
    `LeanPaper.ImportedSection56.DualWeightInvariance,
    `LeanPaper.ImportedSection56.FiniteKreinCone,
    `LeanPaper.ImportedSection56.PositiveSlopeSpectrum,
    `LeanPaper.ImportedSection56.ZetaSevenBound,
    `LeanPaper.ImportedSection3.ExactTaylor,
    `LeanPaper.ImportedSection56.DualBasisCongruence,
    `LeanPaper.ImportedSection56.DualRowSeparation,
    `LeanPaper.ImportedSection56.FullMonomial,
    `LeanPaper.ImportedSection56.DualNonsingularDegree,
    `LeanPaper.ImportedSection56.DualNullspace,
    `LeanPaper.ImportedSection56.SelectedMonomial,
    `LeanPaper.ImportedSection56.UnimodularMonomial,
    `LeanPaper.Section5DualSpectrum]
  let mut roots : Array Name := #[]
  for (decl, _) in env.constants do
    if let some idx := env.getModuleIdxFor? decl then
      if projectModules.contains env.header.moduleNames[idx.toNat]! then
        roots := roots.push decl
  if roots.isEmpty then
    throwError "EMPTY_PROJECT_AUDIT"
  let result := LeanPaper.AxiomWalk.collect env roots
  match LeanPaper.AxiomWalk.check result allowed with
  | .error msg => throwError msg
  | .ok () => pure ()
  let theoremCount := roots.foldl (fun n decl => match env.find? decl with
    | some (.thmInfo _) => n + 1
    | _ => n) (0 : Nat)
  IO.println s!"AUDITED_PROJECT_THEOREM_DECLARATIONS={theoremCount}"
  IO.println s!"AUDITED_PROJECT_DECLARATIONS={roots.size}"
  IO.println s!"AUDITED_DEPENDENCY_DECLARATIONS={result.visited.toArray.size}"
  IO.println s!"AUDITED_AXIOMS={result.axioms.toArray.toList}"
  IO.println "AXIOM_AUDIT_METHOD=INDEPENDENT_VISITED_SET_GRAPH"
  IO.println "AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS"
