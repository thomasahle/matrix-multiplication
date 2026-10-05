/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.MatrixMultiplication.BiniInterpolation
import AlgebraicComplexity.MatrixMultiplication.BorderRank
import AlgebraicComplexity.MatrixMultiplication.PartialCompression

/-!
# Schönhage's `τ`-theorem for partial matrix multiplication

This module formalizes Arnold Schönhage, *Partial and Total Matrix Multiplication*, SIAM Journal
on Computing **10**(3), 434–455 (1981), **Theorem 4.1**: over an *infinite* field, a tensor of
partial matrix multiplication containing `f` ones and having border rank at most `l` bounds the
exponent of *total* matrix multiplication by

`ω(F) ≤ λ(l, f) = 3 · ln l / ln f`.

`MatrixMultiplication/AsymptoticSum.lean` proves the companion Theorem 7.1 for direct sums of
*total* rectangular products, which holds over an arbitrary field.  As `DESIGN.md` records in its
reference-theorem ladder, the genuinely partial case is different: it carries a separate
infinite-field hypothesis.  Here that hypothesis is used exactly once, in `exists_pmmCompression`,
to produce Vandermonde matrices all of whose maximal minors are invertible (Schönhage's equation
(4.11)).  Schönhage removes it afterwards through his Theorem 2.8 (`ω(F)` depends only on the
characteristic of `F`); that reduction is *not* formalized here, so `[Infinite F]` stays explicit
in every statement below.

The partial tensor itself, its coordinate description, its variable counts and the compression
certificate `PMMCompression` are the ring-level half of the development and live one module lower,
in `AlgebraicComplexity/MatrixMultiplication/PartialCompression.lean`; this module adds everything
that first needs border rank, Bini interpolation and word types.

## Objects

* `pmmProductPositions`, `pmmPowerPositions`: Kronecker products and powers of variable patterns.
* `biniLeftPositions`, `biniRightPositions`: the pattern of Bini's partial `2 × 2` product, the
  example Schönhage uses in his introduction.

See `PartialCompression.lean` for `PMMIndex`, `PMMSpace`, `pmmTerm`, `pmmSupport`,
`partialMatrixMultiplication`, `pmmColumn`, `pmmRow` and `PMMCompression`.

## Principal results

* `borderRankLEAt_partialMatrixMultiplication_pow` (Schönhage Lemma 3.1): a border-rank-`r`
  certificate of leading degree `d` for a pattern gives a border-rank-`r ^ s` certificate of
  leading degree `s * d` for its `s`-fold Kronecker power, whose pattern is the `s`-fold product
  pattern.  `borderRankLE_partialMatrixMultiplication_pow` forgets the degree.
* Together with `PMMCompression.restricts` and `exists_pmmCompression` of
  `PartialCompression.lean` this is the **filling lemma**: a power of a partial tensor restricts
  to a total rectangular matrix-multiplication tensor of computable dimensions.
* `borderRankLEAt_matrixMultiplication_of_type`: the filling lemma packaged at an *arbitrary*
  multiplicity type `a`, producing `BorderRankLEAt (l ^ s) (s * d) ⟨∏ k_j^{a_j}, |Y_a|,
  ∏ n_j^{a_j}⟩`.  Theorem 4.1 below uses it at the volume weights `x_j = k_j n_j`; Coppersmith's
  rectangular construction (1982) uses it at the area weights `x_j = k_j`.
* `matrixMultiplication_volume_rpow_omega_div_three_le_of_borderRankLE`: the rectangular volume
  form of Bini's theorem, `(m n p) ^ (ω / 3) ≤ r`, for constructive border-rank certificates.
* `partialMatrixMultiplication_card_rpow_omega_div_three_le_of_borderRankLE`: **Theorem 4.1** in
  asymptotic-sum form, `f ^ (ω / 3) ≤ l`, with the logarithmic form
  `omega_le_of_borderRankLE_partialMatrixMultiplication`.
* `omega_le_of_borderRankLE_biniPartial` and `omega_lt_of_borderRankLE_biniPartial`: Schönhage's
  headline example.  A border-rank-five certificate for the partial `2 × 2` product with the
  input entry `x₂₂` deleted gives `ω ≤ 3 log 5 / log 6 < 2.695`, improving the bound
  `3 log 10 / log 12 < 2.7799` that the same algorithm yields by elementary gluing.

## Strategy

Fix `s` and expand `f ^ s = (∑_j k_j n_j) ^ s` multinomially.  Some multiplicity type `a` carries
at least a `1 / (s+1)^{|μ|}` fraction of that sum (`Combinatorics/WordType.lean`).  Its type class
`Y ⊆ (Fin s → μ)` consists of the inner multi-indices for which the `s`-fold Kronecker power of
the pattern has exactly `K = ∏_j k_j^{a_j}` variables in the corresponding column and
`N = ∏_j n_j^{a_j}` in the corresponding row; the selected multinomial term is exactly
`|Y| · K · N`.  Generic Vandermonde compression turns the `s`-th power, of border rank at most
`l ^ s`, into the total tensor `⟨K, |Y|, N⟩`, so `(K · |Y| · N) ^ (ω/3) ≤ l ^ s`.  Combining gives
`(f ^ (ω/3)) ^ s ≤ (s+1)^{|μ|} · l ^ s` for every `s`, and the polynomial loss is removed by an
elementary closedness lemma rather than by a limit.

## Layer placement and non-goals

This file belongs to the reusable matrix-multiplication layer of `DESIGN.md`, beside
`AsymptoticSum.lean`, so it must not import a named example.  The Bini corollaries are therefore
stated *conditionally* on a border-rank-five certificate for the pattern
`biniLeftPositions`/`biniRightPositions`.  `AlgebraicComplexity/Examples/Bini.lean` proves that
certificate for its own tensor `biniPartial`, and `standardCoordinateEquiv_biniPartial` together
with `eq_partialMatrixMultiplication_of_coordinates` identifies the two tensors; that bridge
belongs to the client layer.

Deliberately out of scope: Schönhage's Theorem 2.8 (`ω(F) = ω(F₀)`), which would remove the
infinite-field hypothesis; his Theorem 7.1 for direct sums of *partial* pieces (§7.4), which needs
the disjointness bookkeeping of §7.2–7.3 on top of the machinery developed here; and the sharper
Stirling optimization of §4.4, which only improves the polynomial loss that the closedness lemma
discards anyway.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

section Reindex

section ReindexData

variable {κ μ ν κ' μ' ν' : Type v}

/-- Legwise coordinate-index equivalence induced by reindexing the three matrix index types. -/
def pmmReindexIndex (eκ : κ ≃ κ') (eμ : μ ≃ μ') (eν : ν ≃ ν') :
    ∀ c, PMMIndex κ μ ν c ≃ PMMIndex κ' μ' ν' c
  | .X => eκ.prodCongr eμ
  | .Y => eμ.prodCongr eν
  | .Z => eν.prodCongr eκ

/-- Reindexing acts on summation triples. -/
def pmmReindexTriple (eκ : κ ≃ κ') (eμ : μ ≃ μ') (eν : ν ≃ ν') :
    (κ × μ × ν) ≃ (κ' × μ' × ν') :=
  eκ.prodCongr (eμ.prodCongr eν)

/-- Reindexing commutes with the coordinate index family of a summation triple. -/
theorem pmmReindexIndex_pmmPoint (eκ : κ ≃ κ') (eμ : μ ≃ μ') (eν : ν ≃ ν')
    (t : κ × μ × ν) (c : Leg) :
    pmmReindexIndex eκ eμ eν c (pmmPoint t c) =
      pmmPoint (pmmReindexTriple eκ eμ eν t) c := by
  cases c <;> rfl

end ReindexData

variable {K : Type u} [CommSemiring K]
variable {κ μ ν κ' μ' ν' : Type v}
variable [Fintype κ] [Fintype μ] [Fintype ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]
variable [Fintype κ'] [Fintype μ'] [Fintype ν'] [DecidableEq κ'] [DecidableEq μ'] [DecidableEq ν']

/-- Legwise linear equivalence of coordinate spaces induced by reindexing. -/
noncomputable def pmmReindexLegEquiv (eκ : κ ≃ κ') (eμ : μ ≃ μ') (eν : ν ≃ ν') (c : Leg) :
    PMMSpace κ μ ν K c ≃ₗ[K] PMMSpace κ' μ' ν' K c :=
  LinearEquiv.funCongrLeft K K (pmmReindexIndex eκ eμ eν c).symm

omit [Fintype κ] [Fintype μ] [Fintype ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]
  [Fintype κ'] [Fintype μ'] [Fintype ν'] [DecidableEq κ'] [DecidableEq μ'] [DecidableEq ν'] in
/-- Unfolding lemma: the reindexing leg equivalence is precomposition with the inverse index
equivalence. -/
@[simp] theorem pmmReindexLegEquiv_apply (eκ : κ ≃ κ') (eμ : μ ≃ μ') (eν : ν ≃ ν') (c : Leg)
    (w : PMMSpace κ μ ν K c) :
    pmmReindexLegEquiv (K := K) eκ eμ eν c w =
      LinearEquiv.funCongrLeft K K (pmmReindexIndex eκ eμ eν c).symm w := rfl

/-- Reindexing the index types transports the support of a partial product. -/
theorem pmmSupport_map (eκ : κ ≃ κ') (eμ : μ ≃ μ') (eν : ν ≃ ν')
    (I : Finset (κ × μ)) (J : Finset (μ × ν)) :
    pmmSupport (I.map (eκ.prodCongr eμ).toEmbedding) (J.map (eμ.prodCongr eν).toEmbedding) =
      (pmmSupport I J).map (pmmReindexTriple eκ eμ eν).toEmbedding := by
  ext t
  obtain ⟨x, j, y⟩ := t
  simp [Finset.mem_map_equiv, pmmReindexTriple, Equiv.prodCongr]

/-- Reindexing the three index types by equivalences carries the partial tensor to the partial
tensor of the transported variable positions. -/
theorem map_pmmReindexLegEquiv_partialMatrixMultiplication
    (eκ : κ ≃ κ') (eμ : μ ≃ μ') (eν : ν ≃ ν')
    (I : Finset (κ × μ)) (J : Finset (μ × ν)) :
    Tensor.map (fun c ↦ (pmmReindexLegEquiv (K := K) eκ eμ eν c).toLinearMap)
        (partialMatrixMultiplication (K := K) I J) =
      partialMatrixMultiplication (K := K)
        (I.map (eκ.prodCongr eμ).toEmbedding) (J.map (eμ.prodCongr eν).toEmbedding) := by
  unfold partialMatrixMultiplication
  rw [map_sum, pmmSupport_map, Finset.sum_map]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Tensor.map_pure]
  congr 1
  funext c
  show pmmReindexLegEquiv (K := K) eκ eμ eν c (pmmTerm (K := K) t c) = _
  rw [pmmTerm_eq_single, pmmTerm_eq_single, pmmReindexLegEquiv_apply,
    funCongrLeft_symm_single, pmmReindexIndex_pmmPoint]
  rfl

end Reindex

section Product

/-- Shuffle two pairs of indices into a pair of index pairs. -/
def pmmPairShuffle (α β γ δ : Type v) : (α × β) × (γ × δ) ≃ (α × γ) × (β × δ) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := by rintro ⟨⟨a, b⟩, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, c⟩, b, d⟩; rfl

/-- Shuffle two summation triples into the summation triple of the product tensor. -/
def pmmTripleShuffle (κ₁ μ₁ ν₁ κ₂ μ₂ ν₂ : Type v) :
    (κ₁ × μ₁ × ν₁) × (κ₂ × μ₂ × ν₂) ≃ (κ₁ × κ₂) × (μ₁ × μ₂) × (ν₁ × ν₂) where
  toFun t := ((t.1.1, t.2.1), (t.1.2.1, t.2.2.1), (t.1.2.2, t.2.2.2))
  invFun t := ((t.1.1, t.2.1.1, t.2.2.1), (t.1.2, t.2.1.2, t.2.2.2))
  left_inv := by rintro ⟨⟨a, b, c⟩, d, e, f⟩; rfl
  right_inv := by rintro ⟨⟨a, d⟩, ⟨b, e⟩, c, f⟩; rfl

/-- The coordinate-index equivalence on each leg of a product of partial matrix tensors. -/
def pmmProductIndexEquiv (κ₁ μ₁ ν₁ κ₂ μ₂ ν₂ : Type v) :
    ∀ c, PMMIndex κ₁ μ₁ ν₁ c × PMMIndex κ₂ μ₂ ν₂ c ≃
      PMMIndex (κ₁ × κ₂) (μ₁ × μ₂) (ν₁ × ν₂) c
  | .X => pmmPairShuffle κ₁ μ₁ κ₂ μ₂
  | .Y => pmmPairShuffle μ₁ ν₁ μ₂ ν₂
  | .Z => pmmPairShuffle ν₁ κ₁ ν₂ κ₂

section Positions

variable {α₁ β₁ α₂ β₂ : Type v}

/-- Variable positions of the Kronecker product of two partially filled matrices. -/
def pmmProductPositions (I₁ : Finset (α₁ × β₁)) (I₂ : Finset (α₂ × β₂)) :
    Finset ((α₁ × α₂) × (β₁ × β₂)) :=
  (I₁ ×ˢ I₂).map (pmmPairShuffle α₁ β₁ α₂ β₂).toEmbedding

/-- A position of a Kronecker product carries a variable exactly when both factors do. -/
@[simp] theorem mem_pmmProductPositions
    {I₁ : Finset (α₁ × β₁)} {I₂ : Finset (α₂ × β₂)} {p : (α₁ × α₂) × (β₁ × β₂)} :
    p ∈ pmmProductPositions I₁ I₂ ↔ (p.1.1, p.2.1) ∈ I₁ ∧ (p.1.2, p.2.2) ∈ I₂ := by
  simp [pmmProductPositions, Finset.mem_map_equiv, pmmPairShuffle]

end Positions

section LegEquiv

variable (κ₁ μ₁ ν₁ κ₂ μ₂ ν₂ : Type v)
variable [Fintype κ₁] [Fintype μ₁] [Fintype ν₁] [DecidableEq κ₁] [DecidableEq μ₁] [DecidableEq ν₁]
variable [Fintype κ₂] [Fintype μ₂] [Fintype ν₂] [DecidableEq κ₂] [DecidableEq μ₂] [DecidableEq ν₂]
variable (K : Type u) [CommSemiring K]

/-- The coordinate-space equivalence on each leg of a product of partial matrix tensors. -/
noncomputable def pmmProductLegEquiv (c : Leg) :
    TensorProduct K (PMMSpace κ₁ μ₁ ν₁ K c) (PMMSpace κ₂ μ₂ ν₂ K c) ≃ₗ[K]
      PMMSpace (κ₁ × κ₂) (μ₁ × μ₂) (ν₁ × ν₂) K c :=
  (coordinateTensorEquiv (K := K)).trans
    (LinearEquiv.funCongrLeft K K (pmmProductIndexEquiv κ₁ μ₁ ν₁ κ₂ μ₂ ν₂ c).symm)

omit [DecidableEq κ₁] [DecidableEq μ₁] [DecidableEq ν₁]
  [DecidableEq κ₂] [DecidableEq μ₂] [DecidableEq ν₂] in
/-- Unfolding lemma: the product leg equivalence pairs coordinates and then reindexes. -/
@[simp] theorem pmmProductLegEquiv_apply (c : Leg)
    (w : TensorProduct K (PMMSpace κ₁ μ₁ ν₁ K c) (PMMSpace κ₂ μ₂ ν₂ K c)) :
    pmmProductLegEquiv κ₁ μ₁ ν₁ κ₂ μ₂ ν₂ K c w =
      LinearEquiv.funCongrLeft K K (pmmProductIndexEquiv κ₁ μ₁ ν₁ κ₂ μ₂ ν₂ c).symm
        (coordinateTensorEquiv (K := K) w) := rfl

end LegEquiv

variable {K : Type u} [CommSemiring K]
variable {κ₁ μ₁ ν₁ κ₂ μ₂ ν₂ : Type v}
variable [Fintype κ₁] [Fintype μ₁] [Fintype ν₁] [DecidableEq κ₁] [DecidableEq μ₁] [DecidableEq ν₁]
variable [Fintype κ₂] [Fintype μ₂] [Fintype ν₂] [DecidableEq κ₂] [DecidableEq μ₂] [DecidableEq ν₂]

/-- On defining pure terms the product equivalence pairs the two summation triples. -/
theorem pmmProductLegEquiv_pmmTerm
    (t₁ : κ₁ × μ₁ × ν₁) (t₂ : κ₂ × μ₂ × ν₂) (c : Leg) :
    pmmProductLegEquiv κ₁ μ₁ ν₁ κ₂ μ₂ ν₂ K c
        (pmmTerm (K := K) t₁ c ⊗ₜ[K] pmmTerm (K := K) t₂ c) =
      pmmTerm (K := K) (pmmTripleShuffle κ₁ μ₁ ν₁ κ₂ μ₂ ν₂ (t₁, t₂)) c := by
  rw [pmmTerm_eq_single, pmmTerm_eq_single, pmmTerm_eq_single, pmmProductLegEquiv_apply,
    coordinateTensorEquiv_single_tmul_single, funCongrLeft_symm_single]
  congr 1
  cases c <;> rfl

/-- Supports multiply under the Kronecker product of partially filled matrices. -/
theorem pmmSupport_pmmProductPositions
    (I₁ : Finset (κ₁ × μ₁)) (J₁ : Finset (μ₁ × ν₁))
    (I₂ : Finset (κ₂ × μ₂)) (J₂ : Finset (μ₂ × ν₂)) :
    pmmSupport (pmmProductPositions I₁ I₂) (pmmProductPositions J₁ J₂) =
      (pmmSupport I₁ J₁ ×ˢ pmmSupport I₂ J₂).map
        (pmmTripleShuffle κ₁ μ₁ ν₁ κ₂ μ₂ ν₂).toEmbedding := by
  ext t
  obtain ⟨⟨x₁, x₂⟩, ⟨j₁, j₂⟩, ⟨y₁, y₂⟩⟩ := t
  simp only [mem_pmmSupport, mem_pmmProductPositions, Finset.mem_map_equiv,
    Finset.mem_product, pmmTripleShuffle, Equiv.coe_fn_symm_mk]
  tauto

/-- Partial matrix-multiplication tensors multiply under the factorwise external product: the
Kronecker product of the two patterns of variable positions describes the product tensor. -/
theorem map_pmmProductLegEquiv_partialMatrixMultiplication
    (I₁ : Finset (κ₁ × μ₁)) (J₁ : Finset (μ₁ × ν₁))
    (I₂ : Finset (κ₂ × μ₂)) (J₂ : Finset (μ₂ × ν₂)) :
    Tensor.map (fun c ↦ (pmmProductLegEquiv κ₁ μ₁ ν₁ κ₂ μ₂ ν₂ K c).toLinearMap)
        (Tensor.external (partialMatrixMultiplication (K := K) I₁ J₁)
          (partialMatrixMultiplication (K := K) I₂ J₂)) =
      partialMatrixMultiplication (K := K)
        (pmmProductPositions I₁ I₂) (pmmProductPositions J₁ J₂) := by
  unfold partialMatrixMultiplication
  rw [pmmSupport_pmmProductPositions, Finset.sum_map, Finset.sum_product]
  have hexternal :
      Tensor.external
          (∑ t₁ ∈ pmmSupport I₁ J₁, pure (K := K) (pmmTerm (K := K) t₁))
          (∑ t₂ ∈ pmmSupport I₂ J₂, pure (K := K) (pmmTerm (K := K) t₂)) =
        ∑ t₁ ∈ pmmSupport I₁ J₁, ∑ t₂ ∈ pmmSupport I₂ J₂,
          Tensor.external (pure (K := K) (pmmTerm (K := K) t₁))
            (pure (K := K) (pmmTerm (K := K) t₂)) := by
    simp only [map_sum, LinearMap.sum_apply]
    exact Finset.sum_comm
  rw [hexternal, map_sum]
  refine Finset.sum_congr rfl fun t₁ _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun t₂ _ ↦ ?_
  rw [external_pure, Tensor.map_pure]
  congr 1
  funext c
  exact pmmProductLegEquiv_pmmTerm (K := K) t₁ t₂ c

end Product

section Power

section Positions

variable {α β : Type v} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Variable positions of the `s`-fold Kronecker power of a partially filled matrix: a position
carries a variable exactly when every one of its coordinates does. -/
def pmmPowerPositions (I : Finset (α × β)) (s : ℕ) : Finset ((Fin s → α) × (Fin s → β)) :=
  Finset.univ.filter fun p ↦ ∀ a, (p.1 a, p.2 a) ∈ I

/-- A position of a Kronecker power carries a variable exactly when every coordinate does. -/
@[simp] theorem mem_pmmPowerPositions {I : Finset (α × β)} {s : ℕ}
    {p : (Fin s → α) × (Fin s → β)} :
    p ∈ pmmPowerPositions I s ↔ ∀ a, (p.1 a, p.2 a) ∈ I := by
  simp [pmmPowerPositions]

/-- Splitting off the first tensor factor of an `s + 1`-fold power. -/
def pmmConsEquiv (α : Type v) (s : ℕ) : α × (Fin s → α) ≃ (Fin (s + 1) → α) :=
  Fin.consEquiv fun _ ↦ α

omit [Fintype α] [DecidableEq α] in
/-- Splitting a word of length `s + 1` into its first letter and its tail. -/
@[simp] theorem pmmConsEquiv_symm_apply (s : ℕ) (z : Fin (s + 1) → α) :
    (pmmConsEquiv α s).symm z = (z 0, fun i ↦ z i.succ) := rfl

/-- One step of the recursion for the variable positions of a Kronecker power. -/
theorem pmmPowerPositions_succ (I : Finset (α × β)) (s : ℕ) :
    (pmmProductPositions I (pmmPowerPositions I s)).map
        ((pmmConsEquiv α s).prodCongr (pmmConsEquiv β s)).toEmbedding =
      pmmPowerPositions I (s + 1) := by
  ext p
  obtain ⟨x, y⟩ := p
  rw [Finset.mem_map_equiv, mem_pmmPowerPositions]
  simp only [Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply,
    pmmConsEquiv_symm_apply, mem_pmmProductPositions, mem_pmmPowerPositions]
  constructor
  · rintro ⟨h0, hrest⟩ a
    exact Fin.cases h0 (fun i ↦ hrest i) a
  · intro h
    exact ⟨h 0, fun i ↦ h i.succ⟩

end Positions

variable {K : Type u} [CommSemiring K]
variable {κ μ ν : Type v}
variable [Fintype κ] [Fintype μ] [Fintype ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

/-- **Powering a partial matrix multiplication** (Schönhage 1981, Lemma 3.1), degree-aware form.
A constructive border-rank certificate of size `r` and leading degree `d` for a partial product
yields one of size `r ^ s` and leading degree `s * d` for its `s`-fold Kronecker power, whose
variable positions are the `s`-fold products of the original patterns.

Retaining the leading degree matters for clients that must extract a coefficient afterwards:
degrees add under the external product, so the `s`-th power costs only the *linear* interpolation
overhead `s * d`, not an exponential one.

Proof sketch: induction on `s`.  The zeroth power is a single pure tensor, an exact rank-one
certificate in degree `0`.  The inductive step takes the external product of the given certificate
with the certificate for the `s`-th power — which multiplies sizes and adds degrees — transports it
through the legwise coordinate equivalence `pmmProductLegEquiv` identifying the product tensor with
the partial tensor of the Kronecker-product pattern, and then reindexes the first coordinate
together with the remaining `s` by `pmmConsEquiv`. -/
theorem borderRankLEAt_partialMatrixMultiplication_pow
    {I : Finset (κ × μ)} {J : Finset (μ × ν)} {r d : ℕ}
    (h : BorderRankLEAt r d (partialMatrixMultiplication (K := K) I J)) (s : ℕ) :
    BorderRankLEAt (r ^ s) (s * d)
      (partialMatrixMultiplication (K := K)
        (pmmPowerPositions I s) (pmmPowerPositions J s)) := by
  induction s with
  | zero =>
      have huniv : pmmSupport (pmmPowerPositions I 0) (pmmPowerPositions J 0) =
          (Finset.univ : Finset ((Fin 0 → κ) × (Fin 0 → μ) × (Fin 0 → ν))) := by
        ext t
        simp
      have hcard : (pmmSupport (pmmPowerPositions I 0) (pmmPowerPositions J 0)).card = 1 := by
        rw [huniv, Finset.card_univ]
        simp
      have hrank := (partialMatrixMultiplication_rankLE (K := K)
        (pmmPowerPositions I 0) (pmmPowerPositions J 0)).toBorderRankLEAt
      rw [hcard] at hrank
      simpa using hrank
  | succ s ih =>
      have hstep : r ^ (s + 1) = r * r ^ s := by ring
      have hdeg : (s + 1) * d = d + s * d := by ring
      rw [hstep, hdeg]
      have hmap := (h.external ih).map
        (fun c ↦ (pmmProductLegEquiv κ μ ν
          (Fin s → κ) (Fin s → μ) (Fin s → ν) K c).toLinearMap)
      rw [map_pmmProductLegEquiv_partialMatrixMultiplication] at hmap
      have hre := hmap.map
        (fun c ↦ (pmmReindexLegEquiv (K := K) (pmmConsEquiv κ s) (pmmConsEquiv μ s)
          (pmmConsEquiv ν s) c).toLinearMap)
      rw [map_pmmReindexLegEquiv_partialMatrixMultiplication,
        pmmPowerPositions_succ, pmmPowerPositions_succ] at hre
      exact hre

/-- **Powering a partial matrix multiplication** (Schönhage 1981, Lemma 3.1).  A constructive
border-rank certificate of size `r` for a partial product yields one of size `r ^ s` for its
`s`-fold Kronecker power, whose variable positions are the `s`-fold products of the original
patterns.

This is `borderRankLEAt_partialMatrixMultiplication_pow` with the leading degree forgotten. -/
theorem borderRankLE_partialMatrixMultiplication_pow
    {I : Finset (κ × μ)} {J : Finset (μ × ν)} {r : ℕ}
    (h : BorderRankLE r (partialMatrixMultiplication (K := K) I J)) (s : ℕ) :
    BorderRankLE (r ^ s)
      (partialMatrixMultiplication (K := K)
        (pmmPowerPositions I s) (pmmPowerPositions J s)) := by
  obtain ⟨d, hd⟩ := h.exists_at
  exact (borderRankLEAt_partialMatrixMultiplication_pow hd s).toBorderRankLE

end Power

section Exponent

variable (F : Type u) [Field F]

/-- Volume form of Bini's theorem for *rectangular* border rank: a border-rank-`r` certificate
for `⟨m,n,p⟩` with positive dimensions gives `(m n p) ^ (ω / 3) ≤ r`.

Proof sketch: the three cyclic rotations of `⟨m,n,p⟩` multiply to the square tensor of side
`m n p`, so the certificate cubes to a size-`r³` certificate at that side; Bini's interpolation
theorem then bounds `ω` by `log (r³) / log (m n p)`, which is the stated inequality after
exponentiating. -/
theorem matrixMultiplication_volume_rpow_omega_div_three_le_of_borderRankLE
    {m n p r : ℕ} (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (hr : 1 ≤ r)
    (h : BorderRankLE r (matrixMultiplication (K := F) m n p)) :
    ((m * n * p : ℕ) : ℝ) ^ (omega F / 3) ≤ (r : ℝ) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  rcases Nat.lt_or_ge 1 (m * n * p) with hP | hP
  · have hc1 := h.matrixMultiplication_cycle
    have hc2 := hc1.matrixMultiplication_cycle
    have hmul := (h.matrixMultiplication_mul hc1).matrixMultiplication_mul hc2
    have e1 : m * p * n = m * n * p := by ring
    have e2 : n * m * p = m * n * p := by ring
    have e3 : p * n * m = m * n * p := by ring
    rw [e1, e2, e3] at hmul
    have hcube : (1 : ℕ) ≤ r * r * r := Nat.mul_pos (Nat.mul_pos hr hr) hr
    have homega := omega_le_log_of_borderRankLE (K := F) hP hcube hmul
    have hPpos : (0 : ℝ) < ((m * n * p : ℕ) : ℝ) := by positivity
    have hlogP : 0 < Real.log ((m * n * p : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast hP)
    have hlogr : Real.log ((r * r * r : ℕ) : ℝ) = 3 * Real.log (r : ℝ) := by
      push_cast
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      ring
    rw [hlogr] at homega
    have homega' : omega F * Real.log ((m * n * p : ℕ) : ℝ) ≤ 3 * Real.log (r : ℝ) := by
      calc omega F * Real.log ((m * n * p : ℕ) : ℝ)
          ≤ (3 * Real.log (r : ℝ) / Real.log ((m * n * p : ℕ) : ℝ)) *
              Real.log ((m * n * p : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right homega hlogP.le
        _ = 3 * Real.log (r : ℝ) := by field_simp
    rw [Real.rpow_def_of_pos hPpos, ← Real.exp_log hrpos]
    apply Real.exp_le_exp.mpr
    have hsplit : Real.log ((m * n * p : ℕ) : ℝ) * (omega F / 3) =
        (omega F * Real.log ((m * n * p : ℕ) : ℝ)) / 3 := by ring
    rw [hsplit]
    linarith
  · have hone : m * n * p = 1 :=
      le_antisymm hP (Nat.mul_pos (Nat.mul_pos hm hn) hp)
    rw [hone]
    simpa using (by exact_mod_cast hr : (1 : ℝ) ≤ (r : ℝ))

end Exponent

section TauTheorem

variable (F : Type u) [Field F] [Infinite F]
variable {κ μ ν : Type v}
variable [Fintype κ] [Fintype μ] [Fintype ν]
variable [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

/-- Enumerate a finite set by an injection from `Fin` of its cardinality. -/
private theorem exists_injective_enumeration {α : Type*} [DecidableEq α] (Y : Finset α) :
    ∃ f : Fin Y.card → α, Function.Injective f ∧ ∀ i, f i ∈ Y := by
  classical
  refine ⟨fun i ↦ ((Finset.equivFinOfCardEq (rfl : Y.card = Y.card)).symm i : α), ?_, ?_⟩
  · intro i j hij
    exact (Finset.equivFinOfCardEq (rfl : Y.card = Y.card)).symm.injective (Subtype.ext hij)
  · intro i
    exact ((Finset.equivFinOfCardEq (rfl : Y.card = Y.card)).symm i).2

/-- Column counts of a Kronecker power are the products of the coordinate column counts. -/
theorem card_pmmColumn_pmmPowerPositions {α β : Type v} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (I : Finset (α × β)) (s : ℕ) (y : Fin s → β) :
    (pmmColumn (pmmPowerPositions I s) y).card = ∏ c, (pmmColumn I (y c)).card := by
  classical
  have hset : pmmColumn (pmmPowerPositions I s) y =
      Fintype.piFinset fun c ↦ pmmColumn I (y c) := by
    ext x
    simp [Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset]

/-- Row counts of a Kronecker power are the products of the coordinate row counts. -/
theorem card_pmmRow_pmmPowerPositions {α β : Type v} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (J : Finset (β × α)) (s : ℕ) (y : Fin s → β) :
    (pmmRow (pmmPowerPositions J s) y).card = ∏ c, (pmmRow J (y c)).card := by
  classical
  have hset : pmmRow (pmmPowerPositions J s) y =
      Fintype.piFinset fun c ↦ pmmRow J (y c) := by
    ext z
    simp [Fintype.mem_piFinset]
  rw [hset, Fintype.card_piFinset]

/-- **The filling lemma at a prescribed multiplicity type** (Schönhage 1981, §4.1–§4.2).

Fix a multiplicity type `a : μ → ℕ` for words of length `s`.  Its type class
`Y = WordType.typeClass s a` consists of the inner multi-indices `Fin s → μ` in which every inner
index `j` occurs exactly `a j` times; for each of them the `s`-fold Kronecker power of the left
pattern has exactly `K = ∏_j k_j ^ a_j` variables in the corresponding column and the right
pattern exactly `N = ∏_j n_j ^ a_j` in the corresponding row.  Generic Vandermonde compression
(`exists_pmmCompression`, the only step needing that the field is infinite) therefore carries the
`s`-th Kronecker power of the partial tensor — of border rank at most `l ^ s` in degree `s * d` —
onto the **total** matrix-multiplication tensor `⟨K, |Y|, N⟩`.

The multiplicity type is an explicit *parameter*.  Schönhage's Theorem 4.1
(`partialMatrixMultiplication_card_rpow_omega_div_three_le_of_borderRankLE` below) instantiates it
at the type selected by `WordType.exists_type_large_weighted_term` for the **volume** weights
`x_j = k_j n_j`, which is what maximizes the number of ones captured.  Coppersmith's rectangular
construction (*Rapid multiplication of rectangular matrices*, SIAM J. Comput. 11(3), 1982) uses the
very same lemma at the **area** weights `x_j = k_j`, which unbalances `K` against `N` and is his
only new step; that is why the type may not be hard-wired here.

No hypothesis on `a` is needed: an unrealizable type simply has an empty class, and the tensor
`⟨K, 0, N⟩` is the zero tensor.  Likewise no non-redundancy hypothesis on the pattern is needed;
the column and row counts enter only through the exact equalities above. -/
theorem borderRankLEAt_matrixMultiplication_of_type
    (I : Finset (κ × μ)) (J : Finset (μ × ν)) {l d : ℕ}
    (h : BorderRankLEAt l d (partialMatrixMultiplication (K := F) I J))
    (s : ℕ) (a : μ → ℕ) :
    BorderRankLEAt (l ^ s) (s * d)
      (matrixMultiplication (K := F)
        (∏ j, (pmmColumn I j).card ^ a j)
        (WordType.typeClass s a).card
        (∏ j, (pmmRow J j).card ^ a j)) := by
  classical
  obtain ⟨sel, hselinj, hselmem⟩ := exists_injective_enumeration (WordType.typeClass s a)
  have hselType : ∀ i, WordType.multiplicity (sel i) = a := fun i ↦
    WordType.mem_typeClass.mp (hselmem i)
  have hcol : ∀ i, (pmmColumn (pmmPowerPositions I s) (sel i)).card =
      ∏ j, (pmmColumn I j).card ^ a j := by
    intro i
    rw [card_pmmColumn_pmmPowerPositions,
      WordType.prod_word_eq_prod_pow (fun j : μ ↦ (pmmColumn I j).card) (sel i), hselType i]
  have hrow : ∀ i, (pmmRow (pmmPowerPositions J s) (sel i)).card =
      ∏ j, (pmmRow J j).card ^ a j := by
    intro i
    rw [card_pmmRow_pmmPowerPositions,
      WordType.prod_word_eq_prod_pow (fun j : μ ↦ (pmmRow J j).card) (sel i), hselType i]
  obtain ⟨Cert⟩ := exists_pmmCompression F
    (pmmPowerPositions I s) (pmmPowerPositions J s) sel hselinj
    (fun i ↦ le_of_eq (hcol i).symm) (fun i ↦ le_of_eq (hrow i).symm)
  have hpow := (borderRankLEAt_partialMatrixMultiplication_pow h s).map Cert.legMap
  rwa [Cert.map_legMap_partialMatrixMultiplication] at hpow

/-- **Schönhage's `τ`-theorem for partial matrix multiplication** (Schönhage, *Partial and total
matrix multiplication*, SIAM J. Comput. 10(3), 1981, Theorem 4.1), in asymptotic-sum form.

Over an **infinite** field, if a partial matrix-multiplication tensor with `f` ones has border
rank at most `l`, then `f ^ (ω / 3) ≤ l`.

The two positivity hypotheses are Schönhage's non-redundancy convention stated just after his
equation (3.5): every inner index really occurs in both factors.

Proof sketch: fix `s` and expand `f^s = (∑_j k_j n_j)^s` multinomially.  Some multiplicity type
`a` carries at least a `1 / (s+1)^{|μ|}` fraction of that sum (`WordType`).  Its type class `Y`
consists of inner multi-indices for which the `s`-fold Kronecker power of the pattern has exactly
`K = ∏_j k_j^{a_j}` variables in the corresponding column and `N = ∏_j n_j^{a_j}` in the
corresponding row, and `|Y| · K · N` is exactly the selected multinomial term.  Generic
Vandermonde compression (`exists_pmmCompression`, the only step using that the field is infinite)
turns the `s`-th power — which has border rank at most `l^s` — into the *total* tensor
`⟨K, |Y|, N⟩`; the rectangular volume form of Bini's theorem gives
`(K·|Y|·N)^(ω/3) ≤ l^s`.  Combining, `(f^(ω/3))^s ≤ (s+1)^{|μ|} · l^s` for every `s`, and the
polynomial factor is removed by `Growth.le_of_pow_succ_le_polynomial_mul_pow_succ`. -/
theorem partialMatrixMultiplication_card_rpow_omega_div_three_le_of_borderRankLE
    (I : Finset (κ × μ)) (J : Finset (μ × ν)) {l : ℕ}
    (hcol : ∀ j : μ, 0 < (pmmColumn I j).card)
    (hrow : ∀ j : μ, 0 < (pmmRow J j).card)
    (hl : 1 ≤ l)
    (h : BorderRankLE l (partialMatrixMultiplication (K := F) I J)) :
    (((pmmSupport I J).card : ℕ) : ℝ) ^ (omega F / 3) ≤ (l : ℝ) := by
  classical
  have hωpos : 0 < omega F / 3 := by
    have h2 := two_le_omega F
    linarith
  have hωnonneg : (0 : ℝ) ≤ omega F / 3 := hωpos.le
  have hωle : omega F / 3 ≤ 1 := by
    have h3 := omega_le_three F
    linarith
  cases isEmpty_or_nonempty μ with
  | inl hempty =>
      have hcard : (pmmSupport I J).card = 0 := by
        rw [Finset.card_eq_zero]
        exact Finset.eq_empty_of_isEmpty _
      rw [hcard, Nat.cast_zero, Real.zero_rpow (ne_of_gt hωpos)]
      positivity
  | inr hne =>
      apply Growth.le_of_pow_succ_le_polynomial_mul_pow_succ
        (ρ := (l : ℝ)) (C := 1) (k := Fintype.card μ) (by positivity) one_pos
      intro n
      rw [one_mul]
      -- The `s`-fold Kronecker power, with `s = n + 1`.
      set s : ℕ := n + 1 with hs
      have hsumx : ∑ j, (((pmmColumn I j).card * (pmmRow J j).card : ℕ) : ℝ) =
          (((pmmSupport I J).card : ℕ) : ℝ) := by
        rw [card_pmmSupport, Nat.cast_sum]
      obtain ⟨aType, haType, hlarge⟩ :=
        WordType.exists_type_large_weighted_term (ι := μ)
          (fun j ↦ (((pmmColumn I j).card * (pmmRow J j).card : ℕ) : ℝ))
          (fun j ↦ by positivity) s
      set Kd : ℕ := ∏ j, (pmmColumn I j).card ^ aType j with hKd
      set Nd : ℕ := ∏ j, (pmmRow J j).card ^ aType j with hNd
      set Y : Finset (Fin s → μ) := WordType.typeClass s aType with hY
      have hprodNat :
          (∏ j, ((pmmColumn I j).card * (pmmRow J j).card) ^ aType j) = Kd * Nd := by
        rw [hKd, hNd, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun j _ ↦ mul_pow _ _ _
      have hprod :
          (∏ j, (((pmmColumn I j).card * (pmmRow J j).card : ℕ) : ℝ) ^ aType j) =
            ((Kd : ℝ) * (Nd : ℝ)) := by
        rw [← Nat.cast_mul, ← hprodNat, Nat.cast_prod]
        exact Finset.prod_congr rfl fun j _ ↦ (Nat.cast_pow _ _).symm
      have hselect : (((pmmSupport I J).card : ℕ) : ℝ) ^ s ≤
          (((s + 1) ^ Fintype.card μ : ℕ) : ℝ) * ((Y.card : ℝ) * ((Kd : ℝ) * (Nd : ℝ))) := by
        rw [← hsumx]
        refine hlarge.trans_eq ?_
        rw [WordType.weightedClassTerm, hprod, hY]
      obtain ⟨dcert, hdcert⟩ := h.exists_at
      have htotal : BorderRankLE (l ^ s)
          (matrixMultiplication (K := F) Kd Y.card Nd) := by
        rw [hKd, hNd, hY]
        exact (borderRankLEAt_matrixMultiplication_of_type F I J hdcert s aType).toBorderRankLE
      have hKdpos : 0 < Kd := by
        rw [hKd]
        exact Finset.prod_pos fun j _ ↦ pow_pos (hcol j) _
      have hNdpos : 0 < Nd := by
        rw [hNd]
        exact Finset.prod_pos fun j _ ↦ pow_pos (hrow j) _
      have hmdpos : 0 < Y.card := by
        rw [hY, Finset.card_pos]
        exact WordType.typeClass_nonempty aType haType
      have hvol := matrixMultiplication_volume_rpow_omega_div_three_le_of_borderRankLE F
        hKdpos hmdpos hNdpos (Nat.one_le_pow s l hl) htotal
      have hfs : (((pmmSupport I J).card : ℕ) : ℝ) ^ s ≤
          (((s + 1) ^ Fintype.card μ : ℕ) : ℝ) * ((Kd * Y.card * Nd : ℕ) : ℝ) := by
        refine hselect.trans_eq ?_
        push_cast
        ring
      have hbig : (1 : ℝ) ≤ (((s + 1) ^ Fintype.card μ : ℕ) : ℝ) := by
        have : 1 ≤ (s + 1) ^ Fintype.card μ := Nat.one_le_pow _ _ (by omega)
        exact_mod_cast this
      calc ((((pmmSupport I J).card : ℕ) : ℝ) ^ (omega F / 3)) ^ (n + 1)
          = ((((pmmSupport I J).card : ℕ) : ℝ) ^ (n + 1)) ^ (omega F / 3) :=
            Real.rpow_pow_comm (by positivity) _ _
        _ ≤ ((((s + 1) ^ Fintype.card μ : ℕ) : ℝ) *
              ((Kd * Y.card * Nd : ℕ) : ℝ)) ^ (omega F / 3) :=
            Real.rpow_le_rpow (by positivity) (by rw [← hs]; exact hfs) hωnonneg
        _ = (((s + 1) ^ Fintype.card μ : ℕ) : ℝ) ^ (omega F / 3) *
              ((Kd * Y.card * Nd : ℕ) : ℝ) ^ (omega F / 3) :=
            Real.mul_rpow (by positivity) (by positivity)
        _ ≤ (((s + 1) ^ Fintype.card μ : ℕ) : ℝ) * ((l ^ s : ℕ) : ℝ) :=
            mul_le_mul (Real.rpow_le_self_of_one_le hbig hωle) hvol
              (by positivity) (by positivity)
        _ = ((n + 2 : ℕ) : ℝ) ^ Fintype.card μ * (l : ℝ) ^ (n + 1) := by
            rw [hs]
            push_cast
            ring

/-- **Schönhage's Theorem 4.1** in exponent form.  Over an infinite field, a partial matrix
multiplication whose tensor has `f ≥ 2` ones and border rank at most `l ≥ 1` bounds the exponent
of *total* matrix multiplication by `ω ≤ 3 · log l / log f`.

This is the numerical form Schönhage writes as `ω(F) ≤ λ(l, f) = 3 ln l / ln f`. -/
theorem omega_le_of_borderRankLE_partialMatrixMultiplication
    (I : Finset (κ × μ)) (J : Finset (μ × ν)) {l : ℕ}
    (hcol : ∀ j : μ, 0 < (pmmColumn I j).card)
    (hrow : ∀ j : μ, 0 < (pmmRow J j).card)
    (hf : 2 ≤ (pmmSupport I J).card)
    (hl : 1 ≤ l)
    (h : BorderRankLE l (partialMatrixMultiplication (K := F) I J)) :
    omega F ≤ 3 * Real.log l / Real.log ((pmmSupport I J).card : ℕ) := by
  have hkey := partialMatrixMultiplication_card_rpow_omega_div_three_le_of_borderRankLE
    F I J hcol hrow hl h
  have hfone : (1 : ℝ) < (((pmmSupport I J).card : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 < (pmmSupport I J).card)
  have hlogf : 0 < Real.log (((pmmSupport I J).card : ℕ) : ℝ) := Real.log_pos hfone
  have hlpos : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hlog : (omega F / 3) * Real.log (((pmmSupport I J).card : ℕ) : ℝ) ≤ Real.log (l : ℝ) := by
    have h1 : Real.log ((((pmmSupport I J).card : ℕ) : ℝ) ^ (omega F / 3)) ≤
        Real.log (l : ℝ) := Real.log_le_log (by positivity) hkey
    rwa [Real.log_rpow (by linarith)] at h1
  rw [le_div_iff₀ hlogf]
  have hsplit : (omega F / 3) * Real.log (((pmmSupport I J).card : ℕ) : ℝ) =
      (omega F * Real.log (((pmmSupport I J).card : ℕ) : ℝ)) / 3 := by ring
  rw [hsplit] at hlog
  linarith

end TauTheorem

section BiniPattern

/-- The variable positions of Bini's partially filled left `2 × 2` factor: every entry except the
deleted input `x₂₂`. -/
def biniLeftPositions : Finset (Fin 2 × Fin 2) :=
  Finset.univ.filter fun p ↦ p ≠ (1, 1)

/-- Bini's right `2 × 2` factor carries variables in every position. -/
def biniRightPositions : Finset (Fin 2 × Fin 2) := Finset.univ

/-- Bini's pattern has six ones: the six summation triples `(i,j,k)` with `(i,j) ≠ (2,2)`. -/
theorem card_pmmSupport_bini :
    (pmmSupport biniLeftPositions biniRightPositions).card = 6 := by decide

/-- Every column of Bini's left factor carries a variable. -/
theorem pmmColumn_biniLeftPositions_card_pos (j : Fin 2) :
    0 < (pmmColumn biniLeftPositions j).card := by
  revert j
  decide

/-- Every row of Bini's right factor carries a variable. -/
theorem pmmRow_biniRightPositions_card_pos (j : Fin 2) :
    0 < (pmmRow biniRightPositions j).card := by
  revert j
  decide

/-- **Schönhage's exponent bound from Bini's partial algorithm** (1981, §1 and §4).  Over an
infinite field, a border-rank-five certificate for the partial `2 × 2` product with the input
entry `x₂₂` deleted gives `ω ≤ 3 log 5 / log 6`.

The hypothesis is exactly the classical Bini–Capovani–Romani–Lotti certificate; the regression
client `AlgebraicComplexity/Examples/Bini.lean` proves `BorderRankLE 5 (biniPartial F)`, and
`eq_partialMatrixMultiplication_of_coordinates` identifies `biniPartial F` with the partial
tensor of this pattern.  That identification is deliberately left to the client layer: this
module belongs to the reusable matrix-multiplication theory and must not import a named
example. -/
theorem omega_le_of_borderRankLE_biniPartial (F : Type u) [Field F] [Infinite F]
    (h : BorderRankLE 5
      (partialMatrixMultiplication (K := F) biniLeftPositions biniRightPositions)) :
    omega F ≤ 3 * Real.log 5 / Real.log 6 := by
  have hmain := omega_le_of_borderRankLE_partialMatrixMultiplication F
    biniLeftPositions biniRightPositions
    pmmColumn_biniLeftPositions_card_pos pmmRow_biniRightPositions_card_pos
    (by rw [card_pmmSupport_bini]; norm_num) (by norm_num) h
  rw [card_pmmSupport_bini] at hmain
  exact_mod_cast hmain

/-- Numerical form of Schönhage's headline example: Bini's five-term approximate algorithm for
the partial `2 × 2` product gives `ω < 2.695`, improving the bound `3 log 10 / log 12 < 2.7799`
obtained from the same algorithm by the elementary gluing argument.

Proof sketch: `3 log 5 / log 6 < 159 / 59 < 2.695`, and the first inequality is equivalent to the
exact integer comparison `5 ^ 177 < 6 ^ 159`, which `norm_num` checks. -/
theorem omega_lt_of_borderRankLE_biniPartial (F : Type u) [Field F] [Infinite F]
    (h : BorderRankLE 5
      (partialMatrixMultiplication (K := F) biniLeftPositions biniRightPositions)) :
    omega F < 2.695 := by
  refine lt_of_le_of_lt (omega_le_of_borderRankLE_biniPartial F h) ?_
  have hpowNat : (5 : ℕ) ^ 177 < (6 : ℕ) ^ 159 := by norm_num
  have hpow : ((5 : ℝ) ^ (177 : ℕ)) < ((6 : ℝ) ^ (159 : ℕ)) := by exact_mod_cast hpowNat
  have hlog := Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hlog' : (177 : ℝ) * Real.log 5 < (159 : ℝ) * Real.log 6 := by exact_mod_cast hlog
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ hlog6]
  linarith

end BiniPattern

end AlgebraicComplexity
