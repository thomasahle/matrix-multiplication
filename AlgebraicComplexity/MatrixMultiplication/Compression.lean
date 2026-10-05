/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TypeExtraction
import AlgebraicComplexity.Tensor.IndexedProduct
import AlgebraicComplexity.Tensor.RankCompression

/-!
# Matrix-multiplication compression

A rank-`L` algorithm for `q × q` matrix multiplication has `L` scalar multiplication slots.
Replacing every slot by an independent `P × P` matrix product gives an algorithm for a single
`(q * P) × (q * P)` product.  At the tensor level, `L` independent copies of `⟨P,P,P⟩` therefore
restrict to `⟨qP,qP,qP⟩`.

This is the finite tensor-substitution step used in Schönhage's multiple-compression argument.
It is separate from the asymptotic sum inequality: no limit, entropy estimate, or field hypothesis
is needed here.

Nothing in the argument is square.  `Tensor.RankLE.matrixMultiplication_compression_general`
states it for arbitrary dimensions — a rank-`card ι` certificate for `⟨q₁,q₂,q₃⟩` substitutes
`card ι` independent copies of `⟨A,B,C⟩` into `⟨q₁A, q₂B, q₃C⟩` — and the square lemmas
`matrixMultiplication_compression` and `matrixMultiplication_compression_card` are its
specializations.  The three rank-`F` tensors `⟨1,F,1⟩`, `⟨F,1,1⟩`, `⟨1,1,F⟩` give the workhorse
laws `⊕_F ⟨A,B,C⟩ ⤳ ⟨A, F·B, C⟩` and its two siblings, which are how a rectangular pipeline turns
a direct sum of constituents into a single rectangular product.
-/

namespace AlgebraicComplexity

open Tensor

universe u

variable {K : Type u} [CommSemiring K]

namespace Tensor.Restricts

/-- Three cyclically oriented constant direct sums expand into all triples of constituents.  Every
one of the `card(ι)^3` resulting constituents restricts to the same square
matrix-multiplication tensor of side length `m * n * p`.

Keeping all cross terms is essential: diagonal symmetrization would retain only `card(ι)` copies,
whereas Schönhage's compression argument uses the full cube of independent copies. -/
theorem matrixMultiplicationConstantDirectSum_symmetrizes
    {ι : Type*} [Fintype ι] (m n p : ℕ) :
    Restricts
      (Tensor.external
        (Tensor.external
          (Tensor.indexedDirectSum
            (fun _ : ι ↦ matrixMultiplication (K := K) m n p))
          (Tensor.indexedDirectSum
            (fun _ : ι ↦ matrixMultiplication (K := K) n p m)))
        (Tensor.indexedDirectSum
          (fun _ : ι ↦ matrixMultiplication (K := K) p m n)))
      (Tensor.indexedDirectSum
        (fun _ : (ι × ι) × ι ↦
          matrixMultiplication (K := K) (m * n * p) (m * n * p) (m * n * p))) := by
  refine (Tensor.Isomorphic.external3_indexedDirectSum
    (K := K)
    (fun _ : ι ↦ matrixMultiplication (K := K) m n p)
    (fun _ : ι ↦ matrixMultiplication (K := K) n p m)
    (fun _ : ι ↦ matrixMultiplication (K := K) p m n)).restricts.trans ?_
  apply Tensor.Restricts.indexedDirectSum
  intro q
  refine Tensor.Restricts.trans
    (W := MMSpace K ((m * n) * p) ((n * p) * m) ((p * m) * n))
    (S := matrixMultiplication (K := K)
      ((m * n) * p) ((n * p) * m) ((p * m) * n)) ?_ ?_
  · exact ⟨mmExternal3Map (K := K) m n p n p m p m n,
      map_mmExternal3Map_matrixMultiplication (K := K) m n p n p m p m n⟩
  · apply matrixMultiplication_restricts <;>
      simp [Nat.mul_comm, Nat.mul_left_comm]

end Tensor.Restricts

namespace Tensor.RankLE

/-- **Rectangular matrix-multiplication compression.** If the *rectangular* tensor `⟨q₁,q₂,q₃⟩`
has rank at most `card ι`, then `card ι` independent `⟨A,B,C⟩` products restrict to one
`⟨q₁A, q₂B, q₃C⟩` product.

This is Schönhage's finite substitution step with no symmetry assumption: a rank decomposition of
`⟨q₁,q₂,q₃⟩` has `card ι` scalar multiplication slots, and substituting an independent copy of
`⟨A,B,C⟩` into each of them computes the external product `⟨q₁,q₂,q₃⟩ ⊠ ⟨A,B,C⟩`, which the
external-product law retypes as `⟨q₁A, q₂B, q₃C⟩`.  Both ingredients
(`Tensor.RankLE.indexedCopies_restricts_external_card` in `Tensor/RankCompression.lean` and
`Tensor.Isomorphic.matrixMultiplication_external` in `MatrixMultiplication/TypeExtraction.lean`)
are already fully rectangular; only this packaging was square.

At `⟨q₁,q₂,q₃⟩ = ⟨1,F,1⟩`, `⟨F,1,1⟩`, `⟨1,1,F⟩` — each of rank `F` by the elementary
decomposition — this specializes to the three workhorse laws that enlarge one dimension of a
direct sum, recorded below as `matrixMultiplication_compression_middle`,
`matrixMultiplication_compression_left` and `matrixMultiplication_compression_right`. -/
theorem matrixMultiplication_compression_general
    {ι : Type*} [Fintype ι] {q₁ q₂ q₃ A B C : ℕ}
    (h : RankLE (Fintype.card ι) (matrixMultiplication (K := K) q₁ q₂ q₃)) :
    Restricts
      (Tensor.indexedDirectSum
        (fun _ : ι ↦ matrixMultiplication (K := K) A B C))
      (matrixMultiplication (K := K) (q₁ * A) (q₂ * B) (q₃ * C)) :=
  (h.indexedCopies_restricts_external_card
      (matrixMultiplication (K := K) A B C)).trans
    (Tensor.Isomorphic.matrixMultiplication_external
      (K := K) q₁ q₂ q₃ A B C).restricts

/-- Numeral-indexed form of rectangular matrix-multiplication compression: the `L` rank slots of
a certificate for `⟨q₁,q₂,q₃⟩` are labelled by `Fin L`. -/
theorem matrixMultiplication_compression_general_fin
    {L q₁ q₂ q₃ A B C : ℕ}
    (h : RankLE L (matrixMultiplication (K := K) q₁ q₂ q₃)) :
    Restricts
      (Tensor.indexedDirectSum
        (fun _ : Fin L ↦ matrixMultiplication (K := K) A B C))
      (matrixMultiplication (K := K) (q₁ * A) (q₂ * B) (q₃ * C)) :=
  matrixMultiplication_compression_general (ι := Fin L) (by simpa using h)

/-- **Matrix-multiplication compression.** If `⟨q,q,q⟩` has rank at most `L`, then `L`
independent `P × P` matrix products restrict to one `(q * P) × (q * P)` matrix product.

This is the square case `⟨q₁,q₂,q₃⟩ = ⟨q,q,q⟩`, `⟨A,B,C⟩ = ⟨P,P,P⟩` of
`matrixMultiplication_compression_general_fin`. -/
theorem matrixMultiplication_compression {L q P : ℕ}
    (h : RankLE L (matrixMultiplication (K := K) q q q)) :
    Restricts
      (Tensor.indexedDirectSum
        (fun _ : Fin L ↦ matrixMultiplication (K := K) P P P))
      (matrixMultiplication (K := K) (q * P) (q * P) (q * P)) :=
  matrixMultiplication_compression_general_fin h

/-- Cardinality-facing form of matrix-multiplication compression.  This is the square case of
`matrixMultiplication_compression_general`. -/
theorem matrixMultiplication_compression_card
    {ι : Type*} [Fintype ι] {q P : ℕ}
    (h : RankLE (Fintype.card ι) (matrixMultiplication (K := K) q q q)) :
    Restricts
      (Tensor.indexedDirectSum
        (fun _ : ι ↦ matrixMultiplication (K := K) P P P))
      (matrixMultiplication (K := K) (q * P) (q * P) (q * P)) :=
  matrixMultiplication_compression_general h

/-- **Widening the middle dimension of a direct sum.**  `F` independent copies of `⟨A,B,C⟩`
restrict to the single product `⟨A, F·B, C⟩`.

This is the compression law at the rank-`F` tensor `⟨1,F,1⟩`, whose elementary decomposition into
`1·F·1 = F` pure terms *is* an optimal algorithm: multiplying a `1 × F` row by an `F × 1` column
uses exactly `F` multiplications.  It is the step that turns the independent constituents produced
by a laser-method zeroing into one honest rectangular product. -/
theorem matrixMultiplication_compression_middle (F A B C : ℕ) :
    Restricts
      (Tensor.indexedDirectSum
        (fun _ : Fin F ↦ matrixMultiplication (K := K) A B C))
      (matrixMultiplication (K := K) A (F * B) C) := by
  have h : RankLE F (matrixMultiplication (K := K) 1 F 1) := by
    simpa using matrixMultiplication_rankLE (K := K) 1 F 1
  exact (matrixMultiplication_compression_general_fin
      (K := K) (A := A) (B := B) (C := C) h).trans
    (Tensor.Isomorphic.matrixMultiplication_congr (K := K)
      (Nat.one_mul A) rfl (Nat.one_mul C)).restricts

/-- **Widening the first outer dimension of a direct sum**: `F` independent copies of `⟨A,B,C⟩`
restrict to `⟨F·A, B, C⟩`, by compression at the rank-`F` tensor `⟨F,1,1⟩`. -/
theorem matrixMultiplication_compression_left (F A B C : ℕ) :
    Restricts
      (Tensor.indexedDirectSum
        (fun _ : Fin F ↦ matrixMultiplication (K := K) A B C))
      (matrixMultiplication (K := K) (F * A) B C) := by
  have h : RankLE F (matrixMultiplication (K := K) F 1 1) := by
    simpa using matrixMultiplication_rankLE (K := K) F 1 1
  exact (matrixMultiplication_compression_general_fin
      (K := K) (A := A) (B := B) (C := C) h).trans
    (Tensor.Isomorphic.matrixMultiplication_congr (K := K)
      rfl (Nat.one_mul B) (Nat.one_mul C)).restricts

/-- **Widening the second outer dimension of a direct sum**: `F` independent copies of `⟨A,B,C⟩`
restrict to `⟨A, B, F·C⟩`, by compression at the rank-`F` tensor `⟨1,1,F⟩`. -/
theorem matrixMultiplication_compression_right (F A B C : ℕ) :
    Restricts
      (Tensor.indexedDirectSum
        (fun _ : Fin F ↦ matrixMultiplication (K := K) A B C))
      (matrixMultiplication (K := K) A B (F * C)) := by
  have h : RankLE F (matrixMultiplication (K := K) 1 1 F) := by
    simpa using matrixMultiplication_rankLE (K := K) 1 1 F
  exact (matrixMultiplication_compression_general_fin
      (K := K) (A := A) (B := B) (C := C) h).trans
    (Tensor.Isomorphic.matrixMultiplication_congr (K := K)
      (Nat.one_mul A) (Nat.one_mul B) rfl).restricts

/-- **Schönhage's finite multiple-compression step.** Three cyclic copies of a direct sum with
`E = card(ι)` equal rectangular constituents expand to `E^3` independent square products.  A
rank-`E^3` algorithm for `q × q` multiplication substitutes those products into its scalar slots
and yields a single square product of side `q * (m * n * p)`. -/
theorem matrixMultiplication_multipleCompression
    {ι : Type*} [Fintype ι] {q : ℕ} (m n p : ℕ)
    (h : RankLE ((Fintype.card ι) ^ 3)
      (matrixMultiplication (K := K) q q q)) :
    Restricts
      (Tensor.external
        (Tensor.external
          (Tensor.indexedDirectSum
            (fun _ : ι ↦ matrixMultiplication (K := K) m n p))
          (Tensor.indexedDirectSum
            (fun _ : ι ↦ matrixMultiplication (K := K) n p m)))
        (Tensor.indexedDirectSum
          (fun _ : ι ↦ matrixMultiplication (K := K) p m n)))
      (matrixMultiplication (K := K)
        (q * (m * n * p)) (q * (m * n * p)) (q * (m * n * p))) := by
  apply (Tensor.Restricts.matrixMultiplicationConstantDirectSum_symmetrizes
    (K := K) (ι := ι) m n p).trans
  apply matrixMultiplication_compression_card
  simpa [Fintype.card_prod, pow_succ, Nat.mul_assoc] using h

/-- Rank-level output of the finite multiple-compression step. -/
theorem matrixMultiplication_multipleCompression_rankLE
    {ι : Type*} [Fintype ι] {q r : ℕ} (m n p : ℕ)
    (hslots : RankLE ((Fintype.card ι) ^ 3)
      (matrixMultiplication (K := K) q q q))
    (hsource : RankLE r
      (Tensor.external
        (Tensor.external
          (Tensor.indexedDirectSum
            (fun _ : ι ↦ matrixMultiplication (K := K) m n p))
          (Tensor.indexedDirectSum
            (fun _ : ι ↦ matrixMultiplication (K := K) n p m)))
        (Tensor.indexedDirectSum
          (fun _ : ι ↦ matrixMultiplication (K := K) p m n)))) :
    RankLE r (matrixMultiplication (K := K)
      (q * (m * n * p)) (q * (m * n * p)) (q * (m * n * p))) :=
  hsource.of_restricts (hslots.matrixMultiplication_multipleCompression m n p)

/-- Complete finite type-compression pipeline.  An optimized rank-`r` certificate for a positive
power of a rectangular direct sum is restricted to one multiplicity type, cyclically symmetrized,
and substituted into a square algorithm whose rank slots equal the cube of the type-class size. -/
theorem matrixMultiplicationDirectSum_type_compression
    {I : Type*} [Fintype I] {r q : ℕ}
    (m n p : I → ℕ) (s : ℕ) (a : I → ℕ)
    (hpower : RankLE r
      (Tensor.power
        (Tensor.indexedDirectSum
          (matrixMultiplicationTensorFamily (K := K) m n p)) (s + 1)))
    (hslots : RankLE
      ((Fintype.card (Tensor.positiveTypeClass I s a)) ^ 3)
      (matrixMultiplication (K := K) q q q)) :
    RankLE (r ^ 3)
      (matrixMultiplication (K := K)
        (q * ((∏ i, m i ^ a i) * (∏ i, n i ^ a i) * (∏ i, p i ^ a i)))
        (q * ((∏ i, m i ^ a i) * (∏ i, n i ^ a i) * (∏ i, p i ^ a i)))
        (q * ((∏ i, m i ^ a i) * (∏ i, n i ^ a i) * (∏ i, p i ^ a i)))) := by
  let M := ∏ i, m i ^ a i
  let N := ∏ i, n i ^ a i
  let P := ∏ i, p i ^ a i
  have hA : RankLE r
      (Tensor.indexedDirectSum
        (fun _q : Tensor.positiveTypeClass I s a ↦
          matrixMultiplication (K := K) M N P)) := by
    simpa [M, N, P] using
      (Tensor.RankLE.matrixMultiplicationDirectSum_type_of_power
        (K := K) m n p s a hpower)
  have hC : RankLE r
      (Tensor.indexedDirectSum
        (fun _q : Tensor.positiveTypeClass I s a ↦
          matrixMultiplication (K := K) P M N)) :=
    hA.matrixMultiplication_indexedDirectSum_cycle
  have hB : RankLE r
      (Tensor.indexedDirectSum
        (fun _q : Tensor.positiveTypeClass I s a ↦
          matrixMultiplication (K := K) N P M)) :=
    hC.matrixMultiplication_indexedDirectSum_cycle
  have hsource : RankLE (r ^ 3)
      (Tensor.external
        (Tensor.external
          (Tensor.indexedDirectSum
            (fun _q : Tensor.positiveTypeClass I s a ↦
              matrixMultiplication (K := K) M N P))
          (Tensor.indexedDirectSum
            (fun _q : Tensor.positiveTypeClass I s a ↦
              matrixMultiplication (K := K) N P M)))
        (Tensor.indexedDirectSum
          (fun _q : Tensor.positiveTypeClass I s a ↦
            matrixMultiplication (K := K) P M N))) := by
    simpa [pow_succ, Nat.mul_assoc] using (hA.external hB).external hC
  simpa [M, N, P] using
    hslots.matrixMultiplication_multipleCompression_rankLE M N P hsource

/-- Rank-level consequence of matrix-multiplication compression. -/
theorem matrixMultiplication_compression_rankLE {L q P r : ℕ}
    (hq : RankLE L (matrixMultiplication (K := K) q q q))
    (hcopies : RankLE r
      (Tensor.indexedDirectSum
        (fun _ : Fin L ↦ matrixMultiplication (K := K) P P P))) :
    RankLE r (matrixMultiplication (K := K) (q * P) (q * P) (q * P)) :=
  hcopies.of_restricts hq.matrixMultiplication_compression

end Tensor.RankLE

end AlgebraicComplexity
