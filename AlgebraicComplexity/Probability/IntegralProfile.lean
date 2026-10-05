import AlgebraicComplexity.Probability.IntegralProfileCore

/-!
# Probability laws represented by integral profiles

This compatibility module re-exports the lightweight integral-profile API from
`IntegralProfileCore`.  Unlike `PositiveIntegralProfile`, zero coordinates are permitted, because
an empirical word type naturally has structural zeroes.

The bridge records the three identities needed by method-of-types arguments:

* entropy is exactly `WordType.profileEntropyNats`;
* deterministic pushforwards are normalized mapped count profiles; and
* multiplying every count by a positive integer leaves the probability law unchanged.
-/
