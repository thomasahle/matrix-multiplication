/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorApproximateRealization

set_option autoImplicit false

/-!
# Exact interface selection inside an approximate interface

The constituent stage of [alman2025more] starts from an interface in which each parent word has
approximately the prescribed complete-split distribution.  An exact rational type is therefore a
legwise sub-selection of that interface, provided the tolerance is nonnegative.  This module
promotes the existing support-containment theorem to the tensor relation actually needed by an
extraction: the approximate selected tensor restricts to its exact selected tensor by variable
zeroing.

The result is deliberately independent of hashing and of the tensor carried by a selected
constituent.  It neither constructs child interfaces nor asserts a copy-count bound.  In
particular, it only proves that the exact parent selector is available inside the approximate
source.  It does not remove the lower-level input holes described in the paper; those require a
later child-identification or repair theorem.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*;
  `papers/sources/2404.16349/constituent.tex:113-147,338-348`.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*, the caveat
  after the mixed cyclic assembly lemma that its local input-profile restrictions remain to be
  proved, `better_bound/paper.tex:2034-2036`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

namespace Restricts

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- If two legwise cuts have nested supports, the outer cut restricts to the inner cut.

This local helper uses only the support inclusion because that is the natural output of the exact
versus approximate profile calculation.  The second cut is still performed by legwise variable
zeroing; no arbitrary support projection is asserted. -/
private theorem select_to_select_of_support_subset
    (P : PartitionedTensor (K := K) (A := A) V)
    (outer inner : ∀ c, A c → Prop)
    [∀ c a, Decidable (outer c a)] [∀ c a, Decidable (inner c a)]
    (hsubset : (P.select inner).support ⊆ (P.select outer).support) :
    Restricts (P.select outer).realize (P.select inner).realize := by
  have hzero := Restricts.partitionedSelect (P.select outer) inner
  have hrealize : ((P.select outer).select inner).realize =
      (P.select inner).realize := by
    classical
    apply PartitionedTensor.realize_eq_of_support_eq
    · ext address
      constructor
      · intro hdouble
        have houter := (PartitionedTensor.mem_select_support
          (P.select outer) inner address).mp hdouble
        have hsource := (PartitionedTensor.mem_select_support
          P outer address).mp houter.1 |>.1
        exact (PartitionedTensor.mem_select_support P inner address).mpr
          ⟨hsource, houter.2⟩
      · intro hexact
        have hinner := (PartitionedTensor.mem_select_support
          P inner address).mp hexact
        exact (PartitionedTensor.mem_select_support
          (P.select outer) inner address).mpr ⟨hsubset hexact, hinner.2⟩
    · intro _address _haddress
      rfl
  rwa [hrealize] at hzero

/-- **An approximate complete-split interface restricts to every exact rational profile it
contains.**

Here `term.toSemantic` is the normalized distribution of the exact count profile.  The theorem
says that selecting that distribution with tolerance `epsilon ≥ 0`, and then zeroing all words
except those of the exact type, gives precisely the exact selected interface term.

Proof sketch: the existing profile calculation proves that the exact selector's support is
contained in the approximate selector's support.  Apply the exact legwise selector once more to
the approximate tensor.  The nested-support identity identifies this double cut with the exact
cut of the original positive power. -/
theorem selectEncodedApproximateInterfaceTerm_to_exact
    {depth n : ℕ}
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    Restricts
      (P.selectEncodedApproximateInterfaceTerm encode
        (term.toSemantic (hmultiplicity.symm ▸ Nat.zero_lt_succ n))
        (by simpa using hmultiplicity) epsilon).realize
      (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).realize := by
  classical
  have hsubset :=
    P.selectEncodedExactInterfaceTerm_support_subset_approximate
      encode term hmultiplicity hepsilon
  unfold PartitionedTensor.selectEncodedApproximateInterfaceTerm
    PartitionedTensor.selectEncodedExactInterfaceTerm
    PartitionedTensor.selectEncodedCompleteSplitProfiles at hsubset ⊢
  exact select_to_select_of_support_subset _ _ _ hsubset

end Restricts

end AlgebraicComplexity.Tensor
