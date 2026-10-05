/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CyclicProduct
import AlgebraicComplexity.Tensor.PositiveExternalPower

/-!
# Tensor-only coherence of cyclic products and positive powers

The value formalism uses the tensor obtained by taking a power of `T` and multiplying its three
cyclic leg orientations.  Ordinary extraction APIs instead naturally take a power of the single
three-orientation product.  This module proves that those sources are legwise isomorphic at every
positive exponent, and supplies dependent-safe transport when two power exponents are equal.

The statement is basis-free and valid over a commutative semiring.  This deliberately narrow file
does not import partitioned tensors: clients such as cyclic laser volume need only source
coherence, while `CyclicProductCoherence.lean` adds the separate realization theorem for a
structured partition.
-/

namespace AlgebraicComplexity.Tensor.Isomorphic

open AlgebraicComplexity.Tensor

universe u v

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Equal power exponents give canonically isomorphic cyclic power products.

This is the dependent-type-safe replacement for rewriting an exponent underneath three tensor
power spaces.  It is useful whenever arithmetic normalization changes a syntactic exponent while
leaving the represented cyclic tensor product unchanged.

Proof sketch: eliminate the equality `a = b`.  The two cyclic products then have definitionally
identical source and target spaces, so the reflexive legwise isomorphism closes the goal. -/
theorem cyclicPowerProduct_congr (T : Tensor3 K V) {a b : ℕ} (h : a = b) :
    Isomorphic (cyclicPowerProduct K T a) (cyclicPowerProduct K T b) := by
  subst b
  exact Isomorphic.refl _

/-- Taking a positive tensor power commutes, up to canonical legwise isomorphism, with the
three-orientation cyclic product.

In human terms,

`T^(n+1) ⊐ cycle(T^(n+1)) ⊐ cycle⁻¹(T^(n+1))`

is the same tensor as

`(T ⊐ cycle(T) ⊐ cycle⁻¹(T))^(n+1)`

after reassociating the tensor-product factors on each leg.

Proof sketch: commute each leg permutation through the positive canonical power, replace the
three resulting powers by the power of their external product twice using
`power_external_positive`, and reverse the latter isomorphism. -/
theorem cyclicPowerProduct_positive
    (T : Tensor3 K V) (n : ℕ) :
    Isomorphic (cyclicPowerProduct K T (n + 1))
      (Tensor.power
        (Tensor.external
          (Tensor.external T (Tensor.permute cycle T))
          (Tensor.permute cycle.symm T))
        (n + 1)) := by
  have hcycle :
      Isomorphic (Tensor.permute cycle (Tensor.power T (n + 1)))
        (Tensor.power (Tensor.permute cycle T) (n + 1)) :=
    (power_permute_positive_unbundled T n cycle).symm
  have hcycleSymm :
      Isomorphic (Tensor.permute cycle.symm (Tensor.power T (n + 1)))
        (Tensor.power (Tensor.permute cycle.symm T) (n + 1)) :=
    (power_permute_positive_unbundled T n cycle.symm).symm
  have hfactors :
      Isomorphic (cyclicPowerProduct K T (n + 1))
        (Tensor.external
          (Tensor.external
            (Tensor.power T (n + 1))
            (Tensor.power (Tensor.permute cycle T) (n + 1)))
          (Tensor.power (Tensor.permute cycle.symm T) (n + 1))) := by
    simpa only [cyclicPowerProduct] using
      ((Isomorphic.refl (Tensor.power T (n + 1))).external hcycle).external hcycleSymm
  have hpower :
      Isomorphic
        (Tensor.power
          (Tensor.external
            (Tensor.external T (Tensor.permute cycle T))
            (Tensor.permute cycle.symm T))
          (n + 1))
        (Tensor.external
          (Tensor.external
            (Tensor.power T (n + 1))
            (Tensor.power (Tensor.permute cycle T) (n + 1)))
          (Tensor.power (Tensor.permute cycle.symm T) (n + 1))) :=
    (power_external_positive
      (Tensor.external T (Tensor.permute cycle T))
      (Tensor.permute cycle.symm T) n).trans
        ((power_external_positive T (Tensor.permute cycle T) n).external
          (Isomorphic.refl (Tensor.power (Tensor.permute cycle.symm T) (n + 1))))
  exact hfactors.trans hpower.symm

end AlgebraicComplexity.Tensor.Isomorphic
