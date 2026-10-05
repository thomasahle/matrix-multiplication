import AxiomAudit.Command
import AlgebraicComplexity.Analysis.ConditionalWordFamilyEntropyGrowth

/-!
# Axiom audit for arbitrary conditional word-family entropy bounds

This focused client checks that both public counting theorems use only the project allowlist.
-/

open AlgebraicComplexity

#assert_axioms WordType.card_words_le_conditionalFeatureEntropyLoss_mul_exp
#assert_axioms WordType.card_words_le_conditionalFeatureEntropyLoss_mul_penaltyBase_pow
#assert_axioms WordType.card_words_le_conditionalFeatureEntropyLoss_mul_profileConditionalEntropyBitsBase_pow
