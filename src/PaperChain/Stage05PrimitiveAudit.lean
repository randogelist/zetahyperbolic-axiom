import PaperChain.Stage05PrimitiveBridge

/-!
Strict native axiom audit for the unconditional original primitive polynomial
and the conditional arithmetic chain. `#print axioms` reports all dependencies;
the runner rejects `sorryAx` and `Lean.ofReduceBool` and fails on any compiler
error. The irrationality results are ONLY implications from explicit estimates.
-/

#print axioms ManuscriptChain.GeneralIrrationality.primitivePolynomial_natDegree
#print axioms ManuscriptChain.GeneralIrrationality.primitivePolynomial_eval_pos
#print axioms ManuscriptChain.GeneralIrrationality.irrational_odd_zeta
#print axioms ManuscriptChain.GeneralIrrationality.oddWeightDecayHypothesis_of_affineFamilyDecay
#print axioms ManuscriptChain.LINEAR_FAMILY_IRRATIONALITY
#print axioms PaperChain.stage05_original_integer_primitive_degree
#print axioms PaperChain.stage05_original_integer_primitive_center_pos
#print axioms PaperChain.stage05_fixed_odd_zeta_irrational_if_affine_decay
#print axioms PaperChain.stage05_zeta5_irrational_if_normalized_quadratic_decay
#print axioms PaperChain.stage05_linear_family_irrational_if_decay

#check ManuscriptChain.GeneralIrrationality.AffineFamilyDecay
#check ManuscriptChain.GeneralArithmetic.EventualQuadraticDecay
