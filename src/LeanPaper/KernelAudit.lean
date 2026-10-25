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
import Lean

/-! Transitive allowlist audit for EVERY declaration from the active project
modules. Module ownership includes private/generated declarations. The three
permitted foundational axioms are explicit; sorryAx and custom assumptions
are rejected. A successful audit does not discharge explicit theorem hypotheses
or establish equivalence with a manuscript paragraph. Native execution pending. -/
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
    `ProofAdvances.Corollary_3_6_AllPrincipalMinors]
  let mut count := 0
  for (decl, _) in env.constants do
    if let some idx := env.getModuleIdxFor? decl then
      if projectModules.contains env.header.moduleNames[idx.toNat]! then
        let axioms ← collectAxioms decl
        let extra := axioms.filter (fun ax => !(allowed.contains ax))
        unless extra.isEmpty do
          throwError m!"UNTRUSTED_AXIOMS {decl}: {extra.toList}"
        count := count + 1
  if count == 0 then
    throwError "EMPTY_PROJECT_AUDIT"
  liftIO <| IO.println s!"AUDITED_PROJECT_DECLARATIONS={count}"
  liftIO <| IO.println "AXIOM_AUDIT_ACCEPTED=ALL_PROJECT_DECLARATIONS"

