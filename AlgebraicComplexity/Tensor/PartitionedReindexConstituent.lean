/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedPowerExternalInterchange

set_option autoImplicit false

/-!
# Constituents under a partition reindexing

A `PartitionedTensor.ReindexEquiv` identifies two full partitioned tensors after a legwise
renaming of their block labels and linear equivalences of the corresponding block spaces.  This
module records its local consequence: the constituents at matching addresses are isomorphic.

The result is independent of tensor powers and matrix multiplication.  It is the local algebraic
step used by the new raw-cyclic Mode-B specialization in the forthcoming legal-hybrid appendix of
the Total-Weight manuscript (`better_bound/paper.tex`).  It is not a theorem stated in
[alman2025more]; that paper's discussion of partitioned powers and recursive extraction,
`papers/sources/2404.16349/overview.tex:18-40`, supplies only the surrounding construction to
which this elementary reindexing law is applied.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

namespace PartitionedTensor

/-- A reindex equivalence identifies the constituent over an address with the constituent over
its inverse-translated address.

Proof sketch: unpack the legwise block-space equivalences in the reindex certificate and apply
the certificate equality at the selected constituent.  `reindex_constituent` turns the resulting
identity into the required tensor isomorphism. -/
theorem ReindexEquiv.constituent_isomorphic
    {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
    {W : ∀ c, B c → Type (max u v)}
    [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]
    {P : PartitionedTensor (K := K) (A := A) V}
    {Q : PartitionedTensor (K := K) (A := B) W}
    {e : ∀ c, A c ≃ B c} (h : P.ReindexEquiv Q e)
    (address : BlockAddress B) :
    Isomorphic
      (P.constituent ((blockAddressCongr e).symm address))
      (Q.constituent address) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun c ↦ f c (address c), ?_⟩
  change map (fun c ↦ (f c (address c)).toLinearMap)
      (P.constituent ((blockAddressCongr e).symm address)) = Q.constituent address
  have hconstituent := congrArg (fun R ↦ R.constituent address) hf
  simpa only [PartitionedTensor.reindex_constituent] using hconstituent

end PartitionedTensor

end AlgebraicComplexity.Tensor
