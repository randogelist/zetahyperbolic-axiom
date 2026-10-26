import PaperChain.Stage03UnconditionalBridge

/-! Native Lean #print-axioms audit of Section 3's analytic assembly,
original-pencil transfer and final bridge. These declarations must not depend
on `sorryAx` or `Lean.ofReduceBool` and must not be counted as arithmetical
irrationality theorems. The runner checks the real compiler output. -/

#print axioms ManuscriptChain.Hyperbolic.poleIntegralIdentity
#print axioms ManuscriptChain.GRAM_POSITIVE
#print axioms ManuscriptChain.MAIN_CHAIN_UNCONDITIONAL
#print axioms ManuscriptChain.EXACT_ZERO_FREE_DISK
#print axioms Zetahyperbolic.GRAM_POSITIVE_ORIGINAL
#print axioms Zetahyperbolic.MAIN_CHAIN_UNCONDITIONAL
#print axioms Zetahyperbolic.ORIGINAL_EXACT_ZERO_FREE_DISK
#print axioms PaperChain.stage03_original_gram_unconditional
#print axioms PaperChain.stage03_original_exact_zero_free_disk
#print axioms PaperChain.stage03_unconditional_general_statement
