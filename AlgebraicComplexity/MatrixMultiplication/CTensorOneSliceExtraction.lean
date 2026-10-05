/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CTensorExtraction
import AlgebraicComplexity.MatrixMultiplication.CTensorOneSliceFusion

/-!
# Extracting a fused one-slice tensor from a shared partition fiber

This module composes the two finite semantic interfaces used by zero-coordinate laser-method
constituents.  A `CTensor.FiberRetyping` first gives one global source map with independent `X`
and `Y` blocks and a genuinely shared `Z` map.  If every mapped constituent is the same canonical
one-slice tensor `⟨1,d,1⟩`, the one-slice fusion theorem then produces the single tensor
`⟨1,h*d,1⟩`.

The theorem assumes only pointwise constituent identities.  In particular, it does not assume a
restriction or degeneration of the assembled family; that conclusion is constructed here.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace CTensor.FiberRetyping

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Fuse an explicitly retyped shared fiber whose mapped constituents are uniformly
`oneSliceConstituent K d`.

The first restriction is built by `FiberRetyping.restricts_partitioned`; hence the common-`Z`
condition is semantic data in `C`, not an after-the-fact compatibility assumption. -/
theorem restricts_oneSliceMatrixMultiplication
    {P : PartitionedTensor (K := K) (A := A) V}
    {selected : Finset (BlockAddress A)} {h d : ℕ}
    (C : FiberRetyping
      (X := MMSpace K 1 d 1 .X)
      (Y := MMSpace K 1 d 1 .Y)
      (Z := MMSpace K 1 d 1 .Z)
      P selected h)
    (htarget : ∀ i, C.targetConstituent i = CTensor.oneSliceConstituent K d) :
    Restricts (P.withSupport selected).realize
      (matrixMultiplication (K := K) 1 (h * d) 1) := by
  have hfamily : C.targetConstituent = fun _ : Fin h ↦ CTensor.oneSliceConstituent K d :=
    funext htarget
  have hretyped := C.restricts_partitioned
  rw [hfamily] at hretyped
  exact hretyped.trans (CTensor.partitioned_oneSliceMatrixMultiplication_restricts h d)

/-- Full-support form of `restricts_oneSliceMatrixMultiplication`. -/
theorem restricts_oneSliceMatrixMultiplication_of_support
    {P : PartitionedTensor (K := K) (A := A) V} {h d : ℕ}
    (C : FiberRetyping
      (X := MMSpace K 1 d 1 .X)
      (Y := MMSpace K 1 d 1 .Y)
      (Z := MMSpace K 1 d 1 .Z)
      P P.support h)
    (htarget : ∀ i, C.targetConstituent i = CTensor.oneSliceConstituent K d) :
    Restricts P.realize (matrixMultiplication (K := K) 1 (h * d) 1) := by
  simpa [PartitionedTensor.withSupport] using
    C.restricts_oneSliceMatrixMultiplication htarget

end CTensor.FiberRetyping

end AlgebraicComplexity
