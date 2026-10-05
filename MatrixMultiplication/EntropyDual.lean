import AlgebraicComplexity.Probability.MaximumEntropyDual

/-!
# Compatibility import for finite maximum-entropy dual certificates

The reusable implementation now lives in
`AlgebraicComplexity/Probability/MaximumEntropyDual.lean`.  This module preserves the historical
`MatrixMultiplication.EntropyDual` names so existing paper clients keep compiling while new code
imports the reusable probability-layer module directly.
-/

namespace MatrixMultiplication.EntropyDual

export AlgebraicComplexity.MaximumEntropyDual
  (entropy crossEntropy entropyTerm_le_crossEntropy_add entropy_le_crossEntropy
   partition partition_pos gibbs gibbs_pos sum_gibbs log_gibbs
   entropy_le_logPartition_sub_expectation marginal sum_potential_marginal
   coordinateScore coordinateScore_expectation entropyBits partitionTwo coordinateDualBits
   entropyBits_le_coordinateDual IsProbability SameMarginals maximumEntropyBits
   coordinateDualBits_eq_of_sameMarginals maximumEntropyBits_le_coordinateDual
   combinationLossBits combinationLossBits_le_dualGap combinationLoss_le_of_maxEntropy_le)

end MatrixMultiplication.EntropyDual
