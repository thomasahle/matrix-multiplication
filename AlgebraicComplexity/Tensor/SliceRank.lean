/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Coordinates
import AlgebraicComplexity.Tensor.Rank
import AlgebraicComplexity.Tensor.Restriction
import AlgebraicComplexity.Tensor.Concise
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Slice rank of three-legged tensors

This file defines slice decompositions and slice rank for the trilinear tensors of
`Tensor.Basic`, mirroring the certificate-list style of `Tensor.Rank`, and proves Tao's
diagonal lower bound: the slice rank of the diagonal (unit) tensor on a finite index type
equals the number of diagonal entries.

## Definitions

* `SliceTermAlong c T`: the tensor `T` factors through a single vector on leg `c`; concretely,
  `T` is a finite sum of pure tensors that all share the same component `v` on leg `c`.  This is
  the elementary form of "`T` lies in the line spanned by `v` tensored with the tensor product
  of the two remaining legs".
* `SliceRankLE r T`: an explicit certificate that `T` is the sum of at most `r` slice terms,
  stored as a list of `(leg, tensor)` pairs, each a slice term along its designated leg.
* `sliceRank T`: the least such `r`, via `Nat.find`, mirroring `Tensor.rank`.
* `diagonalTensor K ι`: the diagonal tensor `∑ i, e_i ⊗ e_i ⊗ e_i` in the standard coordinate
  spaces `ι → K` on all three legs.
* `SliceRankAlongLE c r T` and `sliceRankAlong c T`: the same certificate and minimum for
  decompositions all of whose terms are slice terms along the *single* leg `c`.  These are the
  invariants `S_x`, `S_y`, `S_z` of Alman's thesis, §5.1.
* `maxSliceRankAlong T`: the largest of the three single-leg slice ranks,
  `max {S_x T, S_y T, S_z T}`.

## Main results

* Basic calculus over a commutative semiring: pure tensors are slice terms along every leg,
  slice-rank certificates are monotone, subadditive, stable under scalars, legwise linear maps,
  restriction (`SliceRankLE.of_restricts`) and leg permutation, and every rank certificate is a
  slice-rank certificate (`RankLE.sliceRankLE`), hence `sliceRank T ≤ rank T`.
* `SliceRankLE.card_le_of_diagonalTensor` (Tao's lower bound): over a field, every slice-rank
  certificate for `diagonalTensor K ι` has at least `Fintype.card ι` terms.  Consequently
  `sliceRank_diagonalTensor : sliceRank (diagonalTensor K ι) = Fintype.card ι` and
  `rank_diagonalTensor : rank (diagonalTensor K ι) = Fintype.card ι`.
* `card_le_sliceRank_of_restricts_diagonalTensor` (finite barrier core): if `T` restricts to the
  diagonal tensor of size `m`, then `m ≤ sliceRank T`.  This is the finite heart of the
  Alman--Vassilevska Williams slice-rank barrier for the laser method: the number of independent
  diagonal blocks extractable from `T` by legwise linear maps is capped by its slice rank.
* The single-leg calculus of Alman's thesis, Lemma 5.1: `sliceRank_le_sliceRankAlong` and
  `sliceRankAlong_le_rank` (part 1), `sliceRankAlong_external_le` (part 2, submultiplicativity of
  `S_c` under external products), `sliceRankAlong_add_le` (part 3),
  `sliceRank_external_le : S (A ⊠ B) ≤ S (A) · max_c S_c (B)` and its mirror image (part 4), and
  `sliceRankAlong_le_card_of_span` / `sliceRankAlong_le_finrank` (part 5, the dimension bound on a
  leg).  `maxSliceRankAlong_external_le` records that, unlike slice rank itself,
  `max_c S_c` *is* submultiplicative; that is what bounds the slice ranks of all tensor powers
  geometrically.
* **The subspace layer.**  `sliceSubmodule c D` is the span of the pure tensors whose leg-`c`
  component lies in the subspace `D ≤ V c`, that is `D ⊗ Y ⊗ Z` and its two rotations, and
  `SliceSumWith c e T` says that `T` splits into one slice term per member of a finite family `e`
  of *prescribed* leg-`c` vectors.  Prescribing the vectors is what makes the predicate closed
  under sums and scalars, so a span induction proves `sliceSumWith_of_mem_sliceSubmodule` and
  hence `sliceRankAlongLE_of_mem_sliceSubmodule`.  Over a field this culminates in
  `sliceRankLE_iff_exists_sliceSubmodules`: `S (T) ≤ r` exactly when `T` lies in
  `A ⊗ Y ⊗ Z + X ⊗ B ⊗ Z + X ⊗ Y ⊗ C` for leg subspaces of total dimension at most `r`.  Only the
  three subspaces are required to be finite-dimensional; the leg spaces themselves are arbitrary.
  `Tensor/SliceRankSaturation.lean` consumes this layer to convert the valuative argument of
  thesis Proposition 5.1 into a slice certificate.

## Proof strategy for the diagonal bound

We follow Tao's streamlined argument, implemented through the dual contractions of
`Tensor.Concise` rather than through explicit two-leg flattenings:

1. `SliceRankLE.exists_contraction_vectors`: from a slice decomposition of `T` we extract vector
   lists `xs`, `ys`, `zs` (the slice vectors of the `X`-, `Y`-, and `Z`-terms) such that for all
   functionals `fx` annihilating `xs` and `fy` annihilating `ys`, the contraction
   `contractZ fx fy T` lies in the span of `zs`.  Indeed each `X`-slice dies under `fx`, each
   `Y`-slice dies under `fy`, and each `Z`-slice contracts into its own line.
2. For `T = diagonalTensor K ι` the contraction with dot-product functionals is the coordinatewise
   product `fun i ↦ a i * b i`, so `a ⊙ b ∈ span zs` whenever `a ⊥ xs` and `b ⊥ ys`.
3. The annihilator of a list of `L.length` vectors in `ι → K` has codimension at most `L.length`
   (`card_le_length_add_finrank_dualKernel`), and every subspace `W ≤ (ι → K)` contains a vector
   whose support has at least `finrank W` nonzero coordinates
   (`exists_forall_ne_zero_finrank_le_card`, proved by a maximal-support exchange
   argument).  Picking such an `a` in the annihilator of `xs`, the multiplication map `b ↦ a ⊙ b`
   on the annihilator of `ys` has image inside `span zs` and kernel supported off the support of
   `a`; rank--nullity then gives `Fintype.card ι ≤ xs.length + ys.length + zs.length`.

## Position in the library and future work

This is a layer-1 tensor-algebra module: it imports only the tensor core (`Rank`, `Restriction`,
`Concise`) and Mathlib, and mentions no named matrix-multiplication construction.  Sources for the
mathematics: T. Tao, "A symmetric formulation of the Croot--Lev--Pach--Ellenberg--Gijswijt capset
bound" (blog post, 2016) and the notation of Blasiak--Church--Cohn--Grochow--Naslund--Sawin--Umans,
"On cap sets and the group-theoretic approach to matrix multiplication" (Discrete Analysis, 2017).
The motivating application is the slice-rank barrier framework of Alman and Vassilevska Williams,
"Limits on All Known (and Some Unknown) Approaches to Matrix Multiplication" (arXiv:1810.08671),
which consumes the diagonal lower bound through its asymptotic version.

Deliberately left to later modules: the asymptotic slice rank of powers, which needs canonical
tensor powers and therefore lives in `Tensor/AsymptoticSliceRank.lean`; monotonicity of slice rank
under general (or monomial) degeneration -- which requires the Zariski-closedness of the
slice-rank-at-most-`r` locus rather than a certificate manipulation -- and the barrier statements
for border rank and asymptotic rank built on those.  The restriction form of the barrier proved
here is exact and unconditional.

## References

* J. Alman, *Limits on the Universal Method for Matrix Multiplication*, Ph.D. thesis, MIT, 2019,
  §5.1 (Lemma 5.1), for the single-leg slice ranks `S_x`, `S_y`, `S_z`.
-/

namespace AlgebraicComplexity.Tensor

open Function Submodule

universe u v w

section Semiring

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- `SliceTermAlong c T` means that the tensor `T` is a slice term along leg `c`: it is a finite
sum of pure tensors that all carry one common vector `v` on leg `c`.  Equivalently, `T` lies in
the image of `M ↦ v ⊗ M` from the tensor product of the two remaining legs. -/
def SliceTermAlong (c : Leg) (T : Tensor3 K V) : Prop :=
  ∃ (v : V c) (factors : List (∀ i, V i)),
    (∀ t ∈ factors, t c = v) ∧ T = (factors.map pure).sum

namespace SliceTermAlong

/-- The zero tensor is a slice term along every leg, witnessed by the empty sum. -/
theorem zero (c : Leg) : SliceTermAlong c (0 : Tensor3 K V) :=
  ⟨0, [], by simp, by simp⟩

/-- A pure tensor is a slice term along every leg: its own component on that leg is the common
slice vector. -/
theorem pure_tensor (c : Leg) (x : ∀ i, V i) :
    SliceTermAlong c (pure (K := K) x) :=
  ⟨x c, [x], by simp, by simp⟩

/-- Scalar multiples of a slice term along `c` are slice terms along `c`: the scalar can be
absorbed into the common `c`-component of every pure summand. -/
theorem smul {c : Leg} {T : Tensor3 K V} (h : SliceTermAlong c T) (a : K) :
    SliceTermAlong c (a • T) := by
  rcases h with ⟨v, factors, hcomm, rfl⟩
  refine ⟨a • v, factors.map (fun t ↦ Function.update t c (a • v)), ?_, ?_⟩
  · intro t' ht'
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp ht'
    simp
  · rw [List.smul_sum, List.map_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t ht ↦ ?_)
    show a • pure (K := K) t = pure (K := K) (Function.update t c (a • v))
    calc
      a • pure (K := K) t
          = a • pure (K := K) (Function.update t c (t c)) := by
            rw [Function.update_eq_self]
      _ = pure (K := K) (Function.update t c (a • t c)) :=
            ((PiTensorProduct.tprod K).map_update_smul t c a (t c)).symm
      _ = pure (K := K) (Function.update t c (a • v)) := by rw [hcomm t ht]

/-- Legwise linear maps send slice terms along `c` to slice terms along `c`: the common vector
`v` is carried to `f c v`.  The direction follows restriction: the source decomposition is mapped
onto a decomposition of the image tensor. -/
theorem map {c : Leg} {T : Tensor3 K V} (h : SliceTermAlong c T)
    (f : ∀ i, V i →ₗ[K] W i) : SliceTermAlong c (Tensor.map f T) := by
  rcases h with ⟨v, factors, hcomm, rfl⟩
  refine ⟨f c v, factors.map (fun t i ↦ f i (t i)), ?_, ?_⟩
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    show f c (t c) = f c v
    rw [hcomm t ht]
  · clear hcomm
    induction factors with
    | nil => simp
    | cons t factors ih =>
        simp only [List.map_cons, List.sum_cons, LinearMap.map_add, map_pure]
        rw [ih]

/-- Helper: an application of a dependent function at propositionally equal indices is the
cast of the application along the index equality. -/
private theorem apply_index_eq {V : Leg → Type v} (t : ∀ i, V i) {i j : Leg}
    (h : i = j) : t i = cast (congrArg V h.symm) (t j) := by
  subst h
  rfl

/-- Permuting the tensor legs by an orientation `e` carries a slice term along `c` to a slice
term along `e c`: the common vector transports along the index identity `e.symm (e c) = c`. -/
theorem permute {c : Leg} {T : Tensor3 K V} (h : SliceTermAlong c T)
    (e : Orientation) : SliceTermAlong (e c) (Tensor.permute e T) := by
  rcases h with ⟨v, factors, hcomm, rfl⟩
  have hc : e.symm (e c) = c := e.symm_apply_apply c
  refine ⟨cast (congrArg V hc.symm) v, factors.map (fun t i ↦ t (e.symm i)), ?_, ?_⟩
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    show t (e.symm (e c)) = cast (congrArg V hc.symm) v
    rw [← hcomm t ht]
    exact apply_index_eq t hc
  · clear hcomm
    induction factors with
    | nil => simp
    | cons t factors ih =>
        simp only [List.map_cons, List.sum_cons, map_add, permute_pure]
        rw [ih]

end SliceTermAlong

/-- `SliceRankLE r T` is a constructive slice-rank upper bound: an explicit list of at most `r`
pairs `(leg, tensor)`, each tensor a slice term along its designated leg, whose sum is `T`. -/
def SliceRankLE (r : ℕ) (T : Tensor3 K V) : Prop :=
  ∃ terms : List (Leg × Tensor3 K V),
    terms.length ≤ r ∧ (∀ p ∈ terms, SliceTermAlong p.1 p.2) ∧
      T = (terms.map Prod.snd).sum

/-- A slice term along any leg has slice rank at most `1`, witnessed by the one-term list. -/
theorem SliceTermAlong.sliceRankLE {c : Leg} {T : Tensor3 K V}
    (h : SliceTermAlong c T) : SliceRankLE 1 T := by
  refine ⟨[(c, T)], by simp, ?_, by simp⟩
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact h

namespace SliceRankLE

/-- The zero tensor has slice rank at most `0`, witnessed by the empty certificate. -/
theorem zero : SliceRankLE 0 (0 : Tensor3 K V) :=
  ⟨[], by simp, by simp, by simp⟩

/-- Slice-rank upper bounds are monotone in the bound. -/
theorem mono {r s : ℕ} {T : Tensor3 K V} (h : SliceRankLE r T) (hrs : r ≤ s) :
    SliceRankLE s T := by
  rcases h with ⟨terms, hlen, hslice, hsum⟩
  exact ⟨terms, hlen.trans hrs, hslice, hsum⟩

/-- A tensor with slice rank at most `0` is the zero tensor. -/
theorem eq_zero {T : Tensor3 K V} (h : SliceRankLE 0 T) : T = 0 := by
  rcases h with ⟨terms, hlen, -, hsum⟩
  cases terms with
  | nil => simpa using hsum
  | cons p terms => simp at hlen

/-- Slice rank is subadditive: concatenating slice certificates of `T` and `S` yields a slice
certificate of `T + S` of length `r + s`. -/
theorem add {r s : ℕ} {T S : Tensor3 K V}
    (hT : SliceRankLE r T) (hS : SliceRankLE s S) :
    SliceRankLE (r + s) (T + S) := by
  rcases hT with ⟨left, hleft, hsleft, rfl⟩
  rcases hS with ⟨right, hright, hsright, rfl⟩
  refine ⟨left ++ right, ?_, ?_, ?_⟩
  · simpa only [List.length_append] using Nat.add_le_add hleft hright
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    exacts [hsleft p h, hsright p h]
  · simp

/-- Scalar multiples do not increase slice rank: rescale every term of the certificate. -/
theorem smul {r : ℕ} {T : Tensor3 K V} (h : SliceRankLE r T) (a : K) :
    SliceRankLE r (a • T) := by
  rcases h with ⟨terms, hlen, hslice, rfl⟩
  refine ⟨terms.map (fun p ↦ (p.1, a • p.2)), by simpa using hlen, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact (hslice p hp).smul a
  · rw [List.smul_sum, List.map_map, List.map_map]
    rfl

/-- Legwise linear maps preserve slice-rank certificates: each slice term of the source maps to
a slice term of the image along the same leg. -/
theorem map {r : ℕ} {T : Tensor3 K V} (h : SliceRankLE r T)
    (f : ∀ i, V i →ₗ[K] W i) : SliceRankLE r (Tensor.map f T) := by
  rcases h with ⟨terms, hlen, hslice, rfl⟩
  refine ⟨terms.map (fun p ↦ (p.1, Tensor.map f p.2)), by simpa using hlen, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact (hslice p hp).map f
  · rw [map_list_sum (Tensor.map f) (terms.map Prod.snd), List.map_map, List.map_map]
    rfl

/-- Slice-rank upper bounds transfer along restriction: if legwise maps carry the source `T` to
the target `S`, then a slice certificate for `T` induces one for `S` of the same length. -/
theorem of_restricts {r : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : SliceRankLE r T) (hTS : Restricts T S) : SliceRankLE r S := by
  rcases hTS with ⟨f, rfl⟩
  exact hT.map f

/-- Reindexing the three tensor legs preserves slice-rank certificates: a slice term along `c`
becomes a slice term along `e c`. -/
theorem permute {r : ℕ} {T : Tensor3 K V} (h : SliceRankLE r T)
    (e : Orientation) : SliceRankLE r (Tensor.permute e T) := by
  rcases h with ⟨terms, hlen, hslice, rfl⟩
  refine ⟨terms.map (fun p ↦ (e p.1, Tensor.permute e p.2)), by simpa using hlen, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact (hslice p hp).permute e
  · rw [List.map_map]
    clear hslice hlen
    induction terms with
    | nil => simp
    | cons p terms ih =>
        simp only [List.map_cons, List.sum_cons, map_add, Function.comp_apply]
        rw [ih]

end SliceRankLE

/-- Every rank certificate is a slice-rank certificate: each pure tensor is a slice term (along
leg `X`, say).  Hence slice rank refines rank. -/
theorem RankLE.sliceRankLE {r : ℕ} {T : Tensor3 K V} (h : RankLE r T) :
    SliceRankLE r T := by
  rcases h with ⟨terms, hlen, rfl⟩
  refine ⟨terms.map (fun t ↦ (Leg.X, pure (K := K) t)), by simpa using hlen, ?_, ?_⟩
  · intro p hp
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hp
    exact SliceTermAlong.pure_tensor _ t
  · rw [List.map_map]
    rfl

/-- Every tensor admits some finite slice decomposition, obtained from any pure-tensor
decomposition. -/
theorem exists_sliceRankLE (T : Tensor3 K V) : ∃ r, SliceRankLE r T := by
  obtain ⟨r, hr⟩ := exists_rankLE T
  exact ⟨r, hr.sliceRankLE⟩

/-- The slice rank of a tensor: the least length of a decomposition into slice terms.  Introduced
by Tao (2016) in the wake of the capset breakthrough; it refines tensor rank and is the invariant
behind the Alman--Vassilevska Williams laser-method barriers. -/
noncomputable def sliceRank (T : Tensor3 K V) : ℕ := by
  classical
  exact Nat.find (exists_sliceRankLE T)

/-- The defining property of `sliceRank`: every tensor has an explicit decomposition into at most
`sliceRank T` slice terms. -/
theorem sliceRank_spec (T : Tensor3 K V) : SliceRankLE (sliceRank T) T := by
  classical
  exact Nat.find_spec (exists_sliceRankLE T)

/-- The numerical slice rank and the constructive certificate contain the same information. -/
theorem sliceRank_le_iff {T : Tensor3 K V} {r : ℕ} :
    sliceRank T ≤ r ↔ SliceRankLE r T := by
  classical
  constructor
  · intro h
    exact (sliceRank_spec T).mono h
  · intro h
    exact Nat.find_min' (exists_sliceRankLE T) h

/-- Slice rank refines rank: `sliceRank T ≤ rank T` for every tensor. -/
theorem sliceRank_le_rank (T : Tensor3 K V) : sliceRank T ≤ rank T :=
  sliceRank_le_iff.mpr (rank_spec T).sliceRankLE

/-- The zero tensor has slice rank exactly `0`. -/
@[simp] theorem sliceRank_zero : sliceRank (0 : Tensor3 K V) = 0 := by
  have h := sliceRank_le_iff.mpr (SliceRankLE.zero (K := K) (V := V))
  omega

/-- A tensor has slice rank `0` if and only if it is the zero tensor. -/
@[simp] theorem sliceRank_eq_zero {T : Tensor3 K V} : sliceRank T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hspec := sliceRank_spec T
    rw [h] at hspec
    exact hspec.eq_zero
  · intro h
    subst h
    exact sliceRank_zero

/-- A pure tensor has slice rank at most `1`. -/
theorem sliceRank_pure_le_one (x : ∀ c, V c) :
    sliceRank (pure (K := K) x) ≤ 1 :=
  sliceRank_le_iff.mpr (SliceTermAlong.pure_tensor Leg.X x).sliceRankLE

/-- Slice rank is subadditive: `sliceRank (T + S) ≤ sliceRank T + sliceRank S`. -/
theorem sliceRank_add_le (T S : Tensor3 K V) :
    sliceRank (T + S) ≤ sliceRank T + sliceRank S :=
  sliceRank_le_iff.mpr ((sliceRank_spec T).add (sliceRank_spec S))

/-- Legwise linear maps cannot increase slice rank. -/
theorem sliceRank_map_le (f : ∀ c, V c →ₗ[K] W c) (T : Tensor3 K V) :
    sliceRank (map f T) ≤ sliceRank T :=
  sliceRank_le_iff.mpr ((sliceRank_spec T).map f)

/-- Permuting tensor legs cannot increase slice rank; since permutations are invertible, slice
rank is in fact invariant under them. -/
theorem sliceRank_permute_le (e : Orientation) (T : Tensor3 K V) :
    sliceRank (permute e T) ≤ sliceRank T :=
  sliceRank_le_iff.mpr ((sliceRank_spec T).permute e)

/-- Restriction cannot increase slice rank: if legwise maps carry the source `T` to the target
`S`, then `sliceRank S ≤ sliceRank T`. -/
theorem sliceRank_restricts_le {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) : sliceRank S ≤ sliceRank T :=
  sliceRank_le_iff.mpr ((sliceRank_spec T).of_restricts h)

/-- Legwise-isomorphic tensors have equal slice rank. -/
theorem sliceRank_isomorphic {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Isomorphic T S) : sliceRank T = sliceRank S := by
  apply Nat.le_antisymm
  · exact sliceRank_restricts_le h.symm.restricts
  · exact sliceRank_restricts_le h.restricts

end Semiring

section Diagonal

variable (K : Type u) [CommSemiring K]
variable (ι : Type w) [Fintype ι] [DecidableEq ι]

/-- The diagonal (unit) tensor of a finite index type `ι` in the standard coordinate spaces:
`∑ i, e_i ⊗ e_i ⊗ e_i`, where `e_i` is the `i`-th standard basis vector of `ι → K`.  It is the
independent sum of `Fintype.card ι` scalar multiplications. -/
noncomputable def diagonalTensor : Tensor3 K (fun _ : Leg ↦ ι → K) :=
  ∑ i, pure (K := K) (fun _ ↦ Pi.single i 1)

/-- The diagonal tensor of size `n` has rank at most `n`, witnessed by its defining sum of pure
tensors. -/
theorem diagonalTensor_rankLE :
    RankLE (Fintype.card ι) (diagonalTensor K ι) :=
  RankLE.fintype_sum_pure fun i ↦ (fun _ ↦ Pi.single i 1)

/-- **The coefficient function of the diagonal tensor**: `⟨|ι|⟩` has coefficient `1` on the
constant triples `(s, s, s)` and `0` elsewhere.  This is the coordinate presentation of
`diagonalTensor`, and it is what identifies it with the coefficient function
`Tensor.diagonalCoefficients` of `Tensor/IndependenceNumber.lean`. -/
@[simp] theorem standardCoordinateEquiv_diagonalTensor (q : ∀ _ : Leg, ι) :
    standardCoordinateEquiv (K := K) (κ := fun _ : Leg ↦ ι) (diagonalTensor K ι) q =
      if ∀ i, q i = q .X then 1 else 0 := by
  classical
  rw [diagonalTensor, map_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun s _ ↦ standardCoordinateEquiv_pure_single (K := K)
    (κ := fun _ : Leg ↦ ι) (fun _ ↦ s) q]
  by_cases hconst : ∀ i, q i = q .X
  · rw [if_pos hconst, Finset.sum_eq_single (q .X)]
    · rw [if_pos]
      funext i
      exact (hconst i).symm
    · intro s _ hs
      rw [if_neg]
      intro hsq
      exact hs (by rw [← hsq])
    · intro hmem
      exact absurd (Finset.mem_univ (q .X)) hmem
  · rw [if_neg hconst]
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    rw [if_neg]
    intro hsq
    exact hconst fun i ↦ by rw [← hsq]

end Diagonal

section Contraction

variable {K : Type u} [Field K]
variable {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- Helper: contracting an `X`-slice term with functionals `fx`, `fy` yields zero as soon as
`fx` annihilates the common `X`-vector, because `fx (t .X) = fx v = 0` in every summand. -/
private theorem contractZ_eq_zero_of_slice_X
    {T : Tensor3 K V} {v : V .X} {factors : List (∀ i, V i)}
    (hcomm : ∀ t ∈ factors, t .X = v) (hT : T = (factors.map pure).sum)
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (hv : fx v = 0) :
    contractZ fx fy T = 0 := by
  subst hT
  rw [map_list_sum]
  apply List.sum_eq_zero
  intro x hx
  rw [List.map_map, List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  show contractZ fx fy (pure (K := K) t) = 0
  rw [contractZ_pure, hcomm t ht, hv, zero_mul, zero_smul]

/-- Helper: contracting a `Y`-slice term dies when `fy` annihilates the common `Y`-vector. -/
private theorem contractZ_eq_zero_of_slice_Y
    {T : Tensor3 K V} {v : V .Y} {factors : List (∀ i, V i)}
    (hcomm : ∀ t ∈ factors, t .Y = v) (hT : T = (factors.map pure).sum)
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) (hv : fy v = 0) :
    contractZ fx fy T = 0 := by
  subst hT
  rw [map_list_sum]
  apply List.sum_eq_zero
  intro x hx
  rw [List.map_map, List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  show contractZ fx fy (pure (K := K) t) = 0
  rw [contractZ_pure, hcomm t ht, hv, mul_zero, zero_smul]

/-- Helper: contracting a `Z`-slice term lands on the line spanned by its common `Z`-vector,
because every summand contracts to a scalar multiple of that vector. -/
private theorem contractZ_mem_span_of_slice_Z
    {T : Tensor3 K V} {v : V .Z} {factors : List (∀ i, V i)}
    (hcomm : ∀ t ∈ factors, t .Z = v) (hT : T = (factors.map pure).sum)
    (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K) :
    contractZ fx fy T ∈ Submodule.span K {v} := by
  subst hT
  rw [map_list_sum]
  apply list_sum_mem
  intro x hx
  rw [List.map_map, List.mem_map] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  show contractZ fx fy (pure (K := K) t) ∈ Submodule.span K {v}
  rw [contractZ_pure, hcomm t ht]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

/-- Helper for `SliceRankLE.exists_contraction_vectors`, by induction on the certificate list:
each `X`- or `Y`-term contributes its slice vector to `xs` or `ys` and dies under annihilating
functionals, while each `Z`-term contributes its slice vector to `zs` and contracts into the
span. -/
private theorem exists_contraction_vectors_aux
    (terms : List (Leg × Tensor3 K V)) :
    (∀ p ∈ terms, SliceTermAlong p.1 p.2) →
      ∃ (xs : List (V .X)) (ys : List (V .Y)) (zs : List (V .Z)),
        xs.length + ys.length + zs.length ≤ terms.length ∧
        ∀ (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K),
          (∀ u ∈ xs, fx u = 0) → (∀ v ∈ ys, fy v = 0) →
          contractZ fx fy ((terms.map Prod.snd).sum) ∈
            Submodule.span K {w | w ∈ zs} := by
  induction terms with
  | nil =>
      intro _
      refine ⟨[], [], [], by simp, ?_⟩
      intro fx fy _ _
      simp only [List.map_nil, List.sum_nil, _root_.map_zero]
      exact Submodule.zero_mem _
  | cons p rest ih =>
      intro hslice
      obtain ⟨c, S⟩ := p
      have hS : SliceTermAlong c S := hslice (c, S) (by simp)
      obtain ⟨xs, ys, zs, hlen, hprop⟩ :=
        ih fun q hq ↦ hslice q (List.mem_cons_of_mem _ hq)
      obtain ⟨v, factors, hcomm, hSeq⟩ := hS
      cases c with
      | X =>
          refine ⟨v :: xs, ys, zs, by simp; omega, ?_⟩
          intro fx fy hfx hfy
          have hfx' : ∀ u ∈ xs, fx u = 0 :=
            fun u hu ↦ hfx u (List.mem_cons_of_mem _ hu)
          have hv : fx v = 0 := hfx v (by simp)
          simp only [List.map_cons, List.sum_cons, map_add]
          rw [contractZ_eq_zero_of_slice_X hcomm hSeq fx fy hv, zero_add]
          exact hprop fx fy hfx' hfy
      | Y =>
          refine ⟨xs, v :: ys, zs, by simp; omega, ?_⟩
          intro fx fy hfx hfy
          have hfy' : ∀ u ∈ ys, fy u = 0 :=
            fun u hu ↦ hfy u (List.mem_cons_of_mem _ hu)
          have hv : fy v = 0 := hfy v (by simp)
          simp only [List.map_cons, List.sum_cons, map_add]
          rw [contractZ_eq_zero_of_slice_Y hcomm hSeq fx fy hv, zero_add]
          exact hprop fx fy hfx hfy'
      | Z =>
          refine ⟨xs, ys, v :: zs, by simp; omega, ?_⟩
          intro fx fy hfx hfy
          have hsub : ({w | w ∈ zs} : Set (V .Z)) ⊆ {w | w ∈ v :: zs} :=
            fun w hw ↦ List.mem_cons_of_mem _ hw
          simp only [List.map_cons, List.sum_cons, map_add]
          refine Submodule.add_mem _ ?_ (Submodule.span_mono hsub (hprop fx fy hfx hfy))
          refine Submodule.span_mono ?_ (contractZ_mem_span_of_slice_Z hcomm hSeq fx fy)
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          subst hw
          exact List.mem_cons_self ..

/-- Contraction certificate extracted from a slice decomposition.  If `T` has slice rank at most
`r`, then there are lists `xs`, `ys`, `zs` of vectors on the three legs with total length at most
`r` (the slice vectors of the decomposition) such that whenever `fx` annihilates every vector of
`xs` and `fy` annihilates every vector of `ys`, the contraction `contractZ fx fy T` lies in the
span of `zs`.

Proof sketch: induct over the certificate list.  An `X`-slice term is a sum of pure tensors with
common `X`-component `u`; contracting with `fx` multiplies every summand by `fx u = 0`.  A
`Y`-slice dies symmetrically under `fy`.  A `Z`-slice term with common `Z`-vector `w` contracts
to a scalar multiple of `w`, hence into the span of the collected `zs`. -/
theorem SliceRankLE.exists_contraction_vectors {r : ℕ} {T : Tensor3 K V}
    (h : SliceRankLE r T) :
    ∃ (xs : List (V .X)) (ys : List (V .Y)) (zs : List (V .Z)),
      xs.length + ys.length + zs.length ≤ r ∧
      ∀ (fx : V .X →ₗ[K] K) (fy : V .Y →ₗ[K] K),
        (∀ u ∈ xs, fx u = 0) → (∀ v ∈ ys, fy v = 0) →
        contractZ fx fy T ∈ Submodule.span K {w | w ∈ zs} := by
  rcases h with ⟨terms, hlen, hslice, rfl⟩
  obtain ⟨xs, ys, zs, hlen', hprop⟩ := exists_contraction_vectors_aux terms hslice
  exact ⟨xs, ys, zs, hlen'.trans hlen, hprop⟩

end Contraction

section DotFunctional

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι]

/-- The dot-product functional of a coordinate vector: `dotFunctional u x = ∑ i, u i * x i`. -/
def dotFunctional (u : ι → K) : (ι → K) →ₗ[K] K :=
  ∑ i, u i • LinearMap.proj i

/-- The dot-product functional evaluates to the coordinatewise product sum. -/
@[simp] theorem dotFunctional_apply (u x : ι → K) :
    dotFunctional u x = ∑ i, u i * x i := by
  simp [dotFunctional]

/-- The dot product is symmetric in its two vectors. -/
theorem dotFunctional_comm (u x : ι → K) :
    dotFunctional u x = dotFunctional x u := by
  simp only [dotFunctional_apply]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- Evaluating the dot-product functional on a standard basis vector reads off a coordinate. -/
@[simp] theorem dotFunctional_single [DecidableEq ι] (u : ι → K) (i : ι) :
    dotFunctional u (Pi.single i 1) = u i := by
  rw [dotFunctional_apply]
  simp [Pi.single_apply, mul_ite]

/-- The joint kernel of the dot-product functionals of the entries of a list `L`: all coordinate
vectors orthogonal to every entry of `L`. -/
def dualKernel (L : List (ι → K)) : Submodule K (ι → K) :=
  LinearMap.ker (LinearMap.pi fun j : Fin L.length ↦ dotFunctional (L.get j))

/-- Membership in `dualKernel L` means orthogonality to every entry of `L`. -/
theorem mem_dualKernel {L : List (ι → K)} {a : ι → K} :
    a ∈ dualKernel L ↔ ∀ u ∈ L, dotFunctional u a = 0 := by
  constructor
  · intro ha u hu
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hu
    have h := congrFun (LinearMap.mem_ker.mp ha) ⟨j, hj⟩
    rw [LinearMap.pi_apply] at h
    simpa [List.get_eq_getElem] using h
  · intro h
    refine LinearMap.mem_ker.mpr ?_
    funext j
    rw [LinearMap.pi_apply]
    exact h (L.get j) (List.get_mem L j)

end DotFunctional

section FieldCoordinates

variable {K : Type u} [Field K]
variable {ι : Type w} [Fintype ι]

/-- The orthogonal complement of a list of `L.length` vectors has codimension at most
`L.length`: `Fintype.card ι ≤ L.length + finrank (dualKernel L)`.

Proof sketch: `dualKernel L` is the kernel of the linear map `(ι → K) → (Fin L.length → K)`
collecting all the dot products, whose range has dimension at most `L.length`; conclude by
rank--nullity. -/
theorem card_le_length_add_finrank_dualKernel (L : List (ι → K)) :
    Fintype.card ι ≤ L.length + Module.finrank K (dualKernel L) := by
  have hker : dualKernel L =
      LinearMap.ker (LinearMap.pi fun j : Fin L.length ↦ dotFunctional (L.get j)) := rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.pi fun j : Fin L.length ↦ dotFunctional (L.get j))
  have hrange : Module.finrank K
      (LinearMap.range (LinearMap.pi fun j : Fin L.length ↦ dotFunctional (L.get j))) ≤
        L.length := by
    have h := Submodule.finrank_le
      (LinearMap.range (LinearMap.pi fun j : Fin L.length ↦ dotFunctional (L.get j)))
    simpa using h
  have hcard : Module.finrank K (ι → K) = Fintype.card ι := by simp
  rw [hker]
  omega

/-- Every subspace of `ι → K` contains a vector with at least `finrank` many nonzero
coordinates, recorded as a finset of coordinates on which the vector does not vanish.

Proof sketch: choose `a ∈ W` whose support finset `S` has maximal cardinality; such a maximum
exists because support sizes are bounded by `Fintype.card ι`.  The restriction map
`W → (S → K)` is injective: a vector `x ∈ W` vanishing on `S` but not everywhere would make the
support of `a + x` strictly larger than `S` (on `S` the sum agrees with `a`; at a nonzero
coordinate of `x` outside `S` the sum agrees with `x`), contradicting maximality.  Hence
`finrank W ≤ card S`. -/
theorem exists_forall_ne_zero_finrank_le_card
    (W : Submodule K (ι → K)) :
    ∃ a ∈ W, ∃ S : Finset ι, (∀ i ∈ S, a i ≠ 0) ∧
      Module.finrank K W ≤ S.card := by
  classical
  set suppF : (ι → K) → Finset ι := fun w ↦ Finset.univ.filter (fun i ↦ w i ≠ 0)
    with hsuppF
  set A : Set ℕ := {n | ∃ w ∈ W, (suppF w).card = n} with hA
  have hAne : A.Nonempty := ⟨(suppF 0).card, 0, W.zero_mem, rfl⟩
  have hAbdd : BddAbove A := by
    refine ⟨Fintype.card ι, ?_⟩
    rintro n ⟨w, -, rfl⟩
    exact (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨a, haW, hacard⟩ : ∃ w ∈ W, (suppF w).card = sSup A :=
    Nat.sSup_mem hAne hAbdd
  have hAmax : ∀ w ∈ W, (suppF w).card ≤ sSup A :=
    fun w hw ↦ le_csSup hAbdd ⟨w, hw, rfl⟩
  set S : Finset ι := suppF a with hS
  -- The coordinate restriction of `W` to `S` is injective.
  have hinj : Function.Injective
      (LinearMap.pi (fun i : S ↦ (LinearMap.proj (i : ι)).comp W.subtype)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hxS : ∀ i ∈ S, (x : ι → K) i = 0 := by
      intro i hi
      have h := congrFun hx ⟨i, hi⟩
      rw [LinearMap.pi_apply] at h
      exact h
    by_contra hne
    obtain ⟨i0, hi0⟩ : ∃ i, (x : ι → K) i ≠ 0 := by
      have hxne : (x : ι → K) ≠ 0 := fun h0 ↦ hne (Subtype.ext h0)
      exact Function.ne_iff.mp hxne
    have hi0S : i0 ∉ S := fun hmem ↦ hi0 (hxS i0 hmem)
    have hbW : a + (x : ι → K) ∈ W := W.add_mem haW x.2
    have hsub : insert i0 S ⊆ suppF (a + (x : ι → K)) := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hjS
      · have ha0 : a j = 0 := by
          by_contra h
          exact hi0S (by simp [hS, hsuppF, h])
        simp only [hsuppF, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
        rw [ha0, zero_add]
        exact hi0
      · have hx0 : (x : ι → K) j = 0 := hxS j hjS
        have haj : a j ≠ 0 := by
          have := hjS
          rw [hS, hsuppF] at this
          simpa using this
        simp only [hsuppF, Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
        rw [hx0, add_zero]
        exact haj
    have hcard2 : S.card + 1 ≤ (suppF (a + (x : ι → K))).card := by
      have h := Finset.card_le_card hsub
      rwa [Finset.card_insert_of_notMem hi0S] at h
    have hmax := hAmax _ hbW
    omega
  have hle : Module.finrank K W ≤ S.card := by
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    simpa [Fintype.card_coe] using h
  refine ⟨a, haW, S, ?_, hle⟩
  intro i hi
  rw [hS, hsuppF] at hi
  simpa using hi

end FieldCoordinates

section DiagonalLowerBound

variable {K : Type u} [Field K]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Contracting the diagonal tensor against functionals on the `X` and `Y` legs produces the
coordinatewise product of their coordinate vectors. -/
theorem contractZ_diagonalTensor (fx fy : (ι → K) →ₗ[K] K) :
    contractZ (V := fun _ : Leg ↦ ι → K) fx fy (diagonalTensor K ι) =
      fun i ↦ fx (Pi.single i 1) * fy (Pi.single i 1) := by
  rw [diagonalTensor, map_sum]
  funext j
  rw [Finset.sum_apply]
  have hterm : ∀ i : ι,
      contractZ (V := fun _ : Leg ↦ ι → K) fx fy
          (pure (K := K) (fun _ ↦ Pi.single i 1)) j =
        (fx (Pi.single i 1) * fy (Pi.single i 1)) * Pi.single (M := fun _ : ι ↦ K) i 1 j := by
    intro i
    rw [contractZ_pure]
    rfl
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i]
  simp [Pi.single_apply, mul_ite]

/-- **Tao's diagonal slice-rank lower bound.**  Over a field, every slice decomposition of the
diagonal tensor on a finite index type `ι` uses at least `Fintype.card ι` slice terms.

Proof sketch (Tao 2016, streamlined): a slice certificate of length `r` yields vector lists
`xs`, `ys`, `zs` with `|xs| + |ys| + |zs| ≤ r` such that `contractZ fx fy` of the diagonal lies
in `span zs` whenever `fx ⊥ xs` and `fy ⊥ ys` (`SliceRankLE.exists_contraction_vectors`).  For
dot-product functionals this contraction is the coordinatewise product, so
`a ⊙ b ∈ span zs` for all `a ∈ dualKernel xs`, `b ∈ dualKernel ys`.  Choose `a ∈ dualKernel xs`
whose nonvanishing coordinate set `S` satisfies `finrank (dualKernel xs) ≤ |S|`; then the linear
map `b ↦ a ⊙ b` on `dualKernel ys` has range inside `span zs` (dimension at most `|zs|`) and
kernel contained in the coordinate subspace vanishing on `S` (dimension at most `n − |S|`).
Rank--nullity on this map, combined with the codimension bounds
`n ≤ |xs| + finrank (dualKernel xs)` and `n ≤ |ys| + finrank (dualKernel ys)`, gives
`n ≤ |xs| + |ys| + |zs| ≤ r`. -/
theorem SliceRankLE.card_le_of_diagonalTensor {r : ℕ}
    (h : SliceRankLE r (diagonalTensor K ι)) : Fintype.card ι ≤ r := by
  classical
  obtain ⟨xs, ys, zs, hlen, hcontr⟩ := h.exists_contraction_vectors
  -- Codimension bounds for the two annihilators.
  have hX := card_le_length_add_finrank_dualKernel xs
  have hY := card_le_length_add_finrank_dualKernel ys
  -- A vector of the X-annihilator with large support.
  obtain ⟨a, haW, S, hS, hSle⟩ :=
    exists_forall_ne_zero_finrank_le_card (dualKernel xs)
  -- Coordinatewise multiplication by `a`, restricted to the Y-annihilator.
  set μ : ↥(dualKernel ys) →ₗ[K] (ι → K) :=
    (LinearMap.pi fun i : ι ↦ a i • LinearMap.proj i).comp
      (dualKernel ys).subtype with hμ
  have hμapply : ∀ (ψ : ↥(dualKernel ys)) (i : ι),
      μ ψ i = a i * (ψ : ι → K) i := by
    intro ψ i
    rw [hμ]
    simp [LinearMap.pi_apply]
  -- The image of `μ` lies in the span of the Z-slice vectors.
  have himg : ∀ ψ : ↥(dualKernel ys),
      μ ψ ∈ Submodule.span K {w | w ∈ zs} := by
    intro ψ
    have hfx : ∀ u ∈ xs, dotFunctional a u = 0 := by
      intro u hu
      rw [dotFunctional_comm]
      exact mem_dualKernel.mp haW u hu
    have hfy : ∀ v ∈ ys, dotFunctional (ψ : ι → K) v = 0 := by
      intro v hv
      rw [dotFunctional_comm]
      exact mem_dualKernel.mp ψ.2 v hv
    have hkey := hcontr (dotFunctional a) (dotFunctional (ψ : ι → K)) hfx hfy
    rw [contractZ_diagonalTensor] at hkey
    have heq : (fun i ↦ dotFunctional a (Pi.single i 1) *
        dotFunctional (ψ : ι → K) (Pi.single i 1)) = μ ψ := by
      funext i
      rw [dotFunctional_single, dotFunctional_single, hμapply]
    rwa [heq] at hkey
  -- Rank--nullity for `μ`.
  have hrn := LinearMap.finrank_range_add_finrank_ker μ
  -- The range has dimension at most the number of Z-slice vectors.
  have hrange : Module.finrank K (LinearMap.range μ) ≤ zs.length := by
    have hsub : LinearMap.range μ ≤ Submodule.span K {w | w ∈ zs} := by
      rintro y ⟨ψ, rfl⟩
      exact himg ψ
    refine (Submodule.finrank_mono hsub).trans ?_
    rw [show ({w | w ∈ zs} : Set (ι → K)) = (↑zs.toFinset : Set (ι → K)) by
      simp [List.coe_toFinset]]
    exact (finrank_span_finset_le_card _).trans (List.toFinset_card_le _)
  -- The kernel injects into the coordinate subspace vanishing on `S`.
  have hker : Module.finrank K (LinearMap.ker μ) + S.card ≤ Fintype.card ι := by
    have hinj : Function.Injective
        (LinearMap.pi (fun i : ↥(Sᶜ) ↦ (LinearMap.proj (i : ι)).comp
          ((dualKernel ys).subtype.comp (LinearMap.ker μ).subtype))) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have hψ : ∀ i, (((x : ↥(dualKernel ys)) : ι → K)) i = 0 := by
        intro i
        by_cases hiS : i ∈ S
        · have hk : μ (x : ↥(dualKernel ys)) = 0 := LinearMap.mem_ker.mp x.2
          have h0 := congrFun hk i
          rw [hμapply] at h0
          rcases mul_eq_zero.mp h0 with h | h
          · exact absurd h (hS i hiS)
          · exact h
        · have h0 := congrFun hx ⟨i, Finset.mem_compl.mpr hiS⟩
          rw [LinearMap.pi_apply] at h0
          exact h0
      exact Subtype.ext (Subtype.ext (funext hψ))
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Finset.card_compl] at h
    have hScard : S.card ≤ Fintype.card ι := Finset.card_le_univ S
    omega
  omega

/-- The slice rank of the diagonal tensor of size `n` is exactly `n`: the defining sum of `n`
pure tensors is an upper certificate and Tao's contraction argument is the matching lower
bound. -/
theorem sliceRank_diagonalTensor :
    sliceRank (diagonalTensor K ι) = Fintype.card ι := by
  apply le_antisymm
  · exact sliceRank_le_iff.mpr (diagonalTensor_rankLE K ι).sliceRankLE
  · exact SliceRankLE.card_le_of_diagonalTensor (sliceRank_spec _)

/-- The rank of the diagonal tensor of size `n` is exactly `n`; the lower bound is inherited
from slice rank. -/
theorem rank_diagonalTensor :
    rank (diagonalTensor K ι) = Fintype.card ι := by
  apply le_antisymm
  · exact rank_le_iff.mpr (diagonalTensor_rankLE K ι)
  · calc
      Fintype.card ι = sliceRank (diagonalTensor K ι) :=
        (sliceRank_diagonalTensor (K := K) (ι := ι)).symm
      _ ≤ rank (diagonalTensor K ι) := sliceRank_le_rank _

/-- **Finite core of the slice-rank barrier** (Alman--Vassilevska Williams, arXiv:1810.08671):
if legwise linear maps carry `T` onto the diagonal tensor of a finite index type `ι` (that is,
`T` restricts to a set of `Fintype.card ι` independent diagonal blocks), then
`Fintype.card ι ≤ sliceRank T`.  Any laser-style argument that extracts an independent diagonal
from `T` by zeroing and projecting is therefore limited by the slice rank of `T`, not by its
rank.  The asymptotic version over tensor powers is deliberate future work. -/
theorem card_le_sliceRank_of_restricts_diagonalTensor
    {V : Leg → Type v} [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
    {T : Tensor3 K V} (h : Restricts T (diagonalTensor K ι)) :
    Fintype.card ι ≤ sliceRank T := by
  calc
    Fintype.card ι = sliceRank (diagonalTensor K ι) :=
      (sliceRank_diagonalTensor (K := K) (ι := ι)).symm
    _ ≤ sliceRank T := sliceRank_restricts_le h

end DiagonalLowerBound

/-! ## Slice rank along one fixed leg

Alman's thesis writes `S_x`, `S_y`, `S_z` for the three *single-leg* slice ranks: `S_c T` is the
least number of `c`-slice terms whose sum is `T`.  A `c`-slice decomposition is the special case of
a slice decomposition all of whose terms are assigned the same leg, so `S T ≤ S_c T`, while every
pure-tensor decomposition is a `c`-slice decomposition, so `S_c T ≤ R T`.

Unlike the mixed-leg slice rank, the single-leg slice ranks are submultiplicative under external
products (`sliceRankAlong_external_le`).  That is what makes them the tool for bounding slice rank
of a product: `sliceRank_external_le` is Lemma 5.1(4) of the thesis,
`S (A ⊗ B) ≤ S (A) · max_c S_c (B)`.
-/

section SliceAlong

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- Helper: a scalar multiple of a pure tensor is again a pure tensor, with the scalar absorbed
into its leg-`d` component. -/
private theorem smul_pure_eq_pure_update (d : Leg) (a : K) (y : ∀ j, V j) :
    a • pure (K := K) y = pure (K := K) (Function.update y d (a • y d)) := by
  calc a • pure (K := K) y
      = a • pure (K := K) (Function.update y d (y d)) := by rw [Function.update_eq_self]
    _ = pure (K := K) (Function.update y d (a • y d)) :=
        ((PiTensorProduct.tprod K).map_update_smul y d a (y d)).symm

/-- Helper: the external product distributes over a list sum in its left factor. -/
private theorem external_list_sum_left (terms : List (Tensor3 K V)) (S : Tensor3 K W) :
    Tensor.external terms.sum S = (terms.map fun T ↦ Tensor.external T S).sum := by
  induction terms with
  | nil => simp
  | cons T terms ih => simp only [List.map_cons, List.sum_cons, external_add_left, ih]

/-- Helper: the external product distributes over a list sum in its right factor. -/
private theorem external_list_sum_right (T : Tensor3 K V) (terms : List (Tensor3 K W)) :
    Tensor.external T terms.sum = (terms.map fun S ↦ Tensor.external T S).sum := by
  induction terms with
  | nil => simp
  | cons S terms ih => simp only [List.map_cons, List.sum_cons, external_add_right, ih]

/-- Helper: the external product of two list sums is the sum over all pairs of one term from each
list. -/
private theorem external_flatMap_sum (left : List (Tensor3 K V)) (right : List (Tensor3 K W)) :
    Tensor.external left.sum right.sum =
      (left.flatMap fun T ↦ right.map fun S ↦ Tensor.external T S).sum := by
  induction left with
  | nil => simp
  | cons T left ih =>
      rw [List.sum_cons, external_add_left, ih, List.flatMap_cons, List.sum_append,
        external_list_sum_right]

/-- `SliceTermWith c v T` is the refinement of `SliceTermAlong` in which the common leg-`c` vector
`v` is *given*: `T` is a finite sum of pure tensors all of whose leg-`c` component is `v`.  Slice
terms along a common leg are not closed under addition, but slice terms with a common *vector*
are, which is what makes this refinement useful in leading-coefficient arguments. -/
def SliceTermWith (c : Leg) (v : V c) (T : Tensor3 K V) : Prop :=
  ∃ factors : List (∀ i, V i), (∀ t ∈ factors, t c = v) ∧ T = (factors.map pure).sum

namespace SliceTermWith

/-- Forgetting the common vector gives a slice term along `c`. -/
theorem sliceTermAlong {c : Leg} {v : V c} {T : Tensor3 K V} (h : SliceTermWith c v T) :
    SliceTermAlong c T := by
  rcases h with ⟨factors, hcomm, hsum⟩
  exact ⟨v, factors, hcomm, hsum⟩

/-- The zero tensor is a slice term with every prescribed leg-`c` vector. -/
theorem zero (c : Leg) (v : V c) : SliceTermWith c v (0 : Tensor3 K V) :=
  ⟨[], by simp, by simp⟩

/-- A pure tensor whose leg-`c` component is `v` is a slice term with vector `v`. -/
theorem pure_tensor {c : Leg} {v : V c} (x : ∀ i, V i) (hx : x c = v) :
    SliceTermWith c v (pure (K := K) x) :=
  ⟨[x], by simpa using hx, by simp⟩

/-- Slice terms with a *common vector* are closed under addition: concatenate the two lists of
pure summands. -/
theorem add {c : Leg} {v : V c} {T S : Tensor3 K V}
    (hT : SliceTermWith c v T) (hS : SliceTermWith c v S) : SliceTermWith c v (T + S) := by
  rcases hT with ⟨left, hleft, rfl⟩
  rcases hS with ⟨right, hright, rfl⟩
  refine ⟨left ++ right, ?_, by simp⟩
  intro t ht
  rcases List.mem_append.mp ht with h | h
  exacts [hleft t h, hright t h]

end SliceTermWith

/-- A slice term along `c` is a slice term with some common leg-`c` vector. -/
theorem SliceTermAlong.exists_sliceTermWith {c : Leg} {T : Tensor3 K V}
    (h : SliceTermAlong c T) : ∃ v, SliceTermWith c v T := h

namespace SliceTermAlong

/-- Slice terms along a common leg `c` are closed under external products: if `T` has common
leg-`c` vector `v` and `S` has common leg-`c` vector `w`, then `T ⊠ S` has common leg-`c` vector
`v ⊗ w`. -/
theorem external {c : Leg} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : SliceTermAlong c T) (hS : SliceTermAlong c S) :
    SliceTermAlong c (Tensor.external T S) := by
  rcases hT with ⟨v, left, hleft, rfl⟩
  rcases hS with ⟨w, right, hright, rfl⟩
  refine ⟨v ⊗ₜ[K] w, left.flatMap fun x ↦ right.map fun y ↦ fun i ↦ x i ⊗ₜ[K] y i, ?_, ?_⟩
  · intro t ht
    rw [List.mem_flatMap] at ht
    obtain ⟨x, hx, ht⟩ := ht
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ht
    show x c ⊗ₜ[K] y c = v ⊗ₜ[K] w
    rw [hleft x hx, hright y hy]
  · rw [external_flatMap_sum]
    simp [List.flatMap_map, List.map_flatMap, Function.comp_def]

end SliceTermAlong

/-- `SliceRankAlongLE c r T` is a constructive upper bound for the leg-`c` slice rank: an explicit
list of at most `r` tensors, each a slice term along the *same* leg `c`, whose sum is `T`. -/
def SliceRankAlongLE (c : Leg) (r : ℕ) (T : Tensor3 K V) : Prop :=
  ∃ terms : List (Tensor3 K V),
    terms.length ≤ r ∧ (∀ S ∈ terms, SliceTermAlong c S) ∧ T = terms.sum

/-- A slice term along `c` has leg-`c` slice rank at most `1`. -/
theorem SliceTermAlong.sliceRankAlongLE {c : Leg} {T : Tensor3 K V}
    (h : SliceTermAlong c T) : SliceRankAlongLE c 1 T := by
  refine ⟨[T], by simp, ?_, by simp⟩
  intro S hS
  rw [List.mem_singleton] at hS
  subst hS
  exact h

namespace SliceRankAlongLE

/-- The zero tensor has leg-`c` slice rank at most `0`, witnessed by the empty certificate. -/
theorem zero (c : Leg) : SliceRankAlongLE c 0 (0 : Tensor3 K V) :=
  ⟨[], by simp, by simp, by simp⟩

/-- Leg-`c` slice-rank upper bounds are monotone in the bound. -/
theorem mono {c : Leg} {r s : ℕ} {T : Tensor3 K V} (h : SliceRankAlongLE c r T) (hrs : r ≤ s) :
    SliceRankAlongLE c s T := by
  rcases h with ⟨terms, hlen, hslice, hsum⟩
  exact ⟨terms, hlen.trans hrs, hslice, hsum⟩

/-- A tensor with leg-`c` slice rank at most `0` is the zero tensor. -/
theorem eq_zero {c : Leg} {T : Tensor3 K V} (h : SliceRankAlongLE c 0 T) : T = 0 := by
  rcases h with ⟨terms, hlen, -, hsum⟩
  cases terms with
  | nil => simpa using hsum
  | cons S terms => simp at hlen

/-- Every leg-`c` slice certificate is a slice certificate of the same length. -/
theorem sliceRankLE {c : Leg} {r : ℕ} {T : Tensor3 K V} (h : SliceRankAlongLE c r T) :
    SliceRankLE r T := by
  rcases h with ⟨terms, hlen, hslice, rfl⟩
  refine ⟨terms.map fun S ↦ (c, S), by simpa using hlen, ?_, ?_⟩
  · intro p hp
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hp
    exact hslice S hS
  · rw [List.map_map]
    simp [Function.comp_def]

/-- Leg-`c` slice rank is subadditive: concatenating certificates of `T` and `S` yields one of
`T + S` of length `r + s`. -/
theorem add {c : Leg} {r s : ℕ} {T S : Tensor3 K V}
    (hT : SliceRankAlongLE c r T) (hS : SliceRankAlongLE c s S) :
    SliceRankAlongLE c (r + s) (T + S) := by
  rcases hT with ⟨left, hleft, hsleft, rfl⟩
  rcases hS with ⟨right, hright, hsright, rfl⟩
  refine ⟨left ++ right, ?_, ?_, ?_⟩
  · simpa only [List.length_append] using Nat.add_le_add hleft hright
  · intro S hS
    rcases List.mem_append.mp hS with h | h
    exacts [hsleft S h, hsright S h]
  · simp

/-- Legwise linear maps preserve leg-`c` slice certificates. -/
theorem map {c : Leg} {r : ℕ} {T : Tensor3 K V} (h : SliceRankAlongLE c r T)
    (f : ∀ i, V i →ₗ[K] W i) : SliceRankAlongLE c r (Tensor.map f T) := by
  rcases h with ⟨terms, hlen, hslice, rfl⟩
  refine ⟨terms.map (Tensor.map f), by simpa using hlen, ?_, ?_⟩
  · intro S hS
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hS
    exact (hslice R hR).map f
  · exact map_list_sum (Tensor.map f) terms

/-- Leg-`c` slice-rank upper bounds transfer along restriction: the source `T` bounds the target
`S`. -/
theorem of_restricts {c : Leg} {r : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : SliceRankAlongLE c r T) (hTS : Restricts T S) : SliceRankAlongLE c r S := by
  rcases hTS with ⟨f, rfl⟩
  exact hT.map f

/-- Reindexing the three tensor legs carries a leg-`c` certificate to a leg-`e c` certificate. -/
theorem permute {c : Leg} {r : ℕ} {T : Tensor3 K V} (h : SliceRankAlongLE c r T)
    (e : Orientation) : SliceRankAlongLE (e c) r (Tensor.permute e T) := by
  rcases h with ⟨terms, hlen, hslice, rfl⟩
  refine ⟨terms.map (Tensor.permute e), by simpa using hlen, ?_, ?_⟩
  · intro S hS
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hS
    exact (hslice R hR).permute e
  · exact map_list_sum (Tensor.permute e) terms

/-- **Submultiplicativity of the single-leg slice rank** (thesis Lemma 5.1(2)): a leg-`c`
certificate of `A` of length `r` and one of `B` of length `s` combine into a leg-`c` certificate of
`A ⊠ B` of length `r * s`, because slice terms along a common leg are closed under external
products. -/
theorem external {c : Leg} {r s : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : SliceRankAlongLE c r T) (hS : SliceRankAlongLE c s S) :
    SliceRankAlongLE c (r * s) (Tensor.external T S) := by
  rcases hT with ⟨left, hleft, hsleft, rfl⟩
  rcases hS with ⟨right, hright, hsright, rfl⟩
  refine ⟨left.flatMap fun T' ↦ right.map fun S' ↦ Tensor.external T' S', ?_, ?_, ?_⟩
  · calc (left.flatMap fun T' ↦ right.map fun S' ↦ Tensor.external T' S').length
        = left.length * right.length := by simp
      _ ≤ r * s := Nat.mul_le_mul hleft hright
  · intro R hR
    rw [List.mem_flatMap] at hR
    obtain ⟨T', hT', hR⟩ := hR
    obtain ⟨S', hS', rfl⟩ := List.mem_map.mp hR
    exact (hsleft T' hT').external (hsright S' hS')
  · exact external_flatMap_sum left right

end SliceRankAlongLE

/-- Every rank certificate is a leg-`c` slice certificate, for every leg `c`: a pure tensor is a
slice term along every leg. -/
theorem RankLE.sliceRankAlongLE {r : ℕ} {T : Tensor3 K V} (c : Leg) (h : RankLE r T) :
    SliceRankAlongLE c r T := by
  rcases h with ⟨terms, hlen, rfl⟩
  refine ⟨terms.map pure, by simpa using hlen, ?_, rfl⟩
  intro S hS
  obtain ⟨t, -, rfl⟩ := List.mem_map.mp hS
  exact SliceTermAlong.pure_tensor c t

/-- Every tensor admits some finite decomposition into slice terms along a fixed leg. -/
theorem exists_sliceRankAlongLE (c : Leg) (T : Tensor3 K V) : ∃ r, SliceRankAlongLE c r T := by
  obtain ⟨r, hr⟩ := exists_rankLE T
  exact ⟨r, hr.sliceRankAlongLE c⟩

/-- The **leg-`c` slice rank** `S_c T` of Alman's thesis: the least number of slice terms along the
single leg `c` whose sum is `T`.  Restricting all terms of a slice decomposition to one leg can only
increase the count, so `sliceRank T ≤ sliceRankAlong c T ≤ rank T`. -/
noncomputable def sliceRankAlong (c : Leg) (T : Tensor3 K V) : ℕ := by
  classical
  exact Nat.find (exists_sliceRankAlongLE c T)

/-- The defining property of `sliceRankAlong`: every tensor has an explicit decomposition into at
most `sliceRankAlong c T` slice terms along `c`. -/
theorem sliceRankAlong_spec (c : Leg) (T : Tensor3 K V) :
    SliceRankAlongLE c (sliceRankAlong c T) T := by
  classical
  exact Nat.find_spec (exists_sliceRankAlongLE c T)

/-- The numerical leg-`c` slice rank and its constructive certificate contain the same
information. -/
theorem sliceRankAlong_le_iff {c : Leg} {T : Tensor3 K V} {r : ℕ} :
    sliceRankAlong c T ≤ r ↔ SliceRankAlongLE c r T := by
  classical
  constructor
  · intro h
    exact (sliceRankAlong_spec c T).mono h
  · intro h
    exact Nat.find_min' (exists_sliceRankAlongLE c T) h

/-- **Thesis Lemma 5.1(1), left half**: slice rank refines the leg-`c` slice rank. -/
theorem sliceRank_le_sliceRankAlong (c : Leg) (T : Tensor3 K V) :
    sliceRank T ≤ sliceRankAlong c T :=
  sliceRank_le_iff.mpr (sliceRankAlong_spec c T).sliceRankLE

/-- **Thesis Lemma 5.1(1), right half**: the leg-`c` slice rank refines ordinary tensor rank. -/
theorem sliceRankAlong_le_rank (c : Leg) (T : Tensor3 K V) : sliceRankAlong c T ≤ rank T :=
  sliceRankAlong_le_iff.mpr ((rank_spec T).sliceRankAlongLE c)

/-- The zero tensor has leg-`c` slice rank exactly `0`. -/
@[simp] theorem sliceRankAlong_zero (c : Leg) : sliceRankAlong c (0 : Tensor3 K V) = 0 := by
  have h := sliceRankAlong_le_iff.mpr (SliceRankAlongLE.zero (K := K) (V := V) c)
  omega

/-- A tensor has leg-`c` slice rank `0` if and only if it is the zero tensor. -/
@[simp] theorem sliceRankAlong_eq_zero {c : Leg} {T : Tensor3 K V} :
    sliceRankAlong c T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hspec := sliceRankAlong_spec c T
    rw [h] at hspec
    exact hspec.eq_zero
  · intro h
    subst h
    exact sliceRankAlong_zero c

/-- **Thesis Lemma 5.1(3)**, single-leg half: `S_c (T + S) ≤ S_c T + S_c S`. -/
theorem sliceRankAlong_add_le (c : Leg) (T S : Tensor3 K V) :
    sliceRankAlong c (T + S) ≤ sliceRankAlong c T + sliceRankAlong c S :=
  sliceRankAlong_le_iff.mpr ((sliceRankAlong_spec c T).add (sliceRankAlong_spec c S))

/-- Legwise linear maps cannot increase the leg-`c` slice rank. -/
theorem sliceRankAlong_map_le (c : Leg) (f : ∀ i, V i →ₗ[K] W i) (T : Tensor3 K V) :
    sliceRankAlong c (Tensor.map f T) ≤ sliceRankAlong c T :=
  sliceRankAlong_le_iff.mpr ((sliceRankAlong_spec c T).map f)

/-- Restriction cannot increase the leg-`c` slice rank: the source `T` has the larger value. -/
theorem sliceRankAlong_restricts_le {c : Leg} {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) : sliceRankAlong c S ≤ sliceRankAlong c T :=
  sliceRankAlong_le_iff.mpr ((sliceRankAlong_spec c T).of_restricts h)

/-- Legwise-isomorphic tensors have equal leg-`c` slice rank. -/
theorem sliceRankAlong_isomorphic {c : Leg} {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Isomorphic T S) : sliceRankAlong c T = sliceRankAlong c S :=
  Nat.le_antisymm (sliceRankAlong_restricts_le h.symm.restricts)
    (sliceRankAlong_restricts_le h.restricts)

/-- Permuting the legs by `e` carries the leg-`c` slice rank to the leg-`e c` slice rank. -/
theorem sliceRankAlong_permute_le (e : Orientation) (c : Leg) (T : Tensor3 K V) :
    sliceRankAlong (e c) (Tensor.permute e T) ≤ sliceRankAlong c T :=
  sliceRankAlong_le_iff.mpr ((sliceRankAlong_spec c T).permute e)

/-- **Thesis Lemma 5.1(2)**: the single-leg slice rank is submultiplicative under external
products, `S_c (A ⊠ B) ≤ S_c (A) · S_c (B)`. -/
theorem sliceRankAlong_external_le (c : Leg) (T : Tensor3 K V) (S : Tensor3 K W) :
    sliceRankAlong c (Tensor.external T S) ≤ sliceRankAlong c T * sliceRankAlong c S :=
  sliceRankAlong_le_iff.mpr ((sliceRankAlong_spec c T).external (sliceRankAlong_spec c S))

end SliceAlong

/-! ### The dimension bound and the product law for slice rank

The single-leg slice rank of a tensor is bounded by the dimension of that leg (thesis Lemma
5.1(5)): expanding the leg-`c` component of every pure summand in a spanning family of `V c`
groups the tensor into one `c`-slice term per family member.  Combined with submultiplicativity of
the single-leg slice ranks this gives the product law `S (A ⊠ B) ≤ S (A) · max_c S_c (B)` of thesis
Lemma 5.1(4), the estimate that drives every upper bound on asymptotic slice rank. -/

section SliceAlongSpan

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- Helper: the cyclic orientation moves every leg, so `cycle c` is a leg different from `c`.
This is how a scalar is parked on a leg other than the slice leg. -/
private theorem ne_cycle (c : Leg) : c ≠ cycle c := by cases c <;> decide

/-- Helper: expanding the leg-`c` component of a pure tensor in a finite family expands the pure
tensor into the corresponding combination of pure tensors whose `c`-component is a family
member. -/
private theorem pure_eq_sum_update {ι : Type*} [Fintype ι] (c : Leg)
    (e : ι → V c) (a : ι → K) (x : ∀ j, V j) (hx : ∑ i, a i • e i = x c) :
    pure (K := K) x = ∑ i, a i • pure (K := K) (Function.update x c (e i)) := by
  classical
  calc pure (K := K) x
      = pure (K := K) (Function.update x c (∑ i, a i • e i)) := by
        rw [hx, Function.update_eq_self]
    _ = ∑ i, pure (K := K) (Function.update x c (a i • e i)) :=
        (PiTensorProduct.tprod K).map_update_sum Finset.univ c (fun i ↦ a i • e i) x
    _ = ∑ i, a i • pure (K := K) (Function.update x c (e i)) :=
        Finset.sum_congr rfl fun i _ ↦
          (PiTensorProduct.tprod K).map_update_smul x c (a i) (e i)

/-- Helper: every tensor decomposes into one `c`-slice term per member of a finite spanning family
`e` of the leg-`c` space, the term attached to `i` having common leg-`c` vector `e i`.

Proof sketch: induction over a pure-tensor decomposition.  A pure tensor is expanded along the
family in its `c`-component by `pure_eq_sum_update`, and each resulting scalar multiple is turned
back into a pure tensor by parking the scalar on the leg `cycle c ≠ c`, which leaves the
`c`-component equal to `e i`.  Sums are handled by concatenating the lists index by index. -/
private theorem exists_sliceTermAlong_family {ι : Type*} [Fintype ι] (c : Leg) (e : ι → V c)
    (hspan : ∀ x : V c, ∃ a : ι → K, ∑ i, a i • e i = x) (T : Tensor3 K V) :
    ∃ factors : ι → List (∀ j, V j),
      (∀ i, ∀ t ∈ factors i, t c = e i) ∧ T = ∑ i, ((factors i).map pure).sum := by
  classical
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro r x
    obtain ⟨a, ha⟩ := hspan (x c)
    set y : ι → ∀ j, V j := fun i ↦ Function.update x c (e i) with hy
    refine ⟨fun i ↦ [Function.update (y i) (cycle c) ((r * a i) • y i (cycle c))], ?_, ?_⟩
    · intro i t ht
      rw [List.mem_singleton] at ht
      subst ht
      rw [Function.update_of_ne (ne_cycle c)]
      simp [hy]
    · have hterm : ∀ i : ι,
          (([Function.update (y i) (cycle c) ((r * a i) • y i (cycle c))]).map
            (pure (K := K))).sum = (r * a i) • pure (K := K) (y i) := by
        intro i
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        exact (smul_pure_eq_pure_update (cycle c) (r * a i) (y i)).symm
      show r • pure (K := K) x = _
      rw [pure_eq_sum_update c e a x ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul]
      exact (hterm i).symm
  · rintro T S ⟨factorsT, hT, rfl⟩ ⟨factorsS, hS, rfl⟩
    refine ⟨fun i ↦ factorsT i ++ factorsS i, ?_, ?_⟩
    · intro i t ht
      rcases List.mem_append.mp ht with h | h
      exacts [hT i t h, hS i t h]
    · simp only [List.map_append, List.sum_append]
      exact (Finset.sum_add_distrib).symm

/-- **Thesis Lemma 5.1(5)**: if the leg-`c` space is spanned by a finite family of `n` vectors,
then every tensor has leg-`c` slice rank at most `n`.

Proof sketch: `exists_sliceTermAlong_family` groups the tensor into one `c`-slice term per family
member; that list of terms is a leg-`c` slice certificate of length `n`. -/
theorem sliceRankAlong_le_card_of_span {ι : Type*} [Fintype ι] (c : Leg) (e : ι → V c)
    (hspan : ⊤ ≤ Submodule.span K (Set.range e)) (T : Tensor3 K V) :
    sliceRankAlong c T ≤ Fintype.card ι := by
  classical
  obtain ⟨factors, hfac, hsum⟩ := exists_sliceTermAlong_family c e
    ((Submodule.top_le_span_range_iff_forall_exists_fun K).mp hspan) T
  refine sliceRankAlong_le_iff.mpr
    ⟨(Finset.univ : Finset ι).toList.map fun i ↦ ((factors i).map pure).sum, by simp, ?_, ?_⟩
  · intro S hS
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hS
    exact ⟨e i, factors i, hfac i, rfl⟩
  · rw [Finset.sum_map_toList]
    exact hsum

/-- A list of tensors of slice rank at most `m` each sums to a tensor of slice rank at most
`length · m`. -/
theorem SliceRankLE.list_sum {m : ℕ} (terms : List (Tensor3 K V))
    (h : ∀ S ∈ terms, SliceRankLE m S) : SliceRankLE (terms.length * m) terms.sum := by
  induction terms with
  | nil => simpa using SliceRankLE.zero (K := K) (V := V)
  | cons S terms ih =>
      rw [List.sum_cons, List.length_cons]
      exact ((h S (List.mem_cons_self ..)).add
        (ih fun R hR ↦ h R (List.mem_cons_of_mem _ hR))).mono (Nat.le_of_eq (by ring))

/-- **Thesis Lemma 5.1(4)**, with an explicit uniform bound on the single-leg slice ranks of the
right factor: if `S_c (S) ≤ m` for every leg `c`, then `S (T ⊠ S) ≤ S (T) · m`.

Proof sketch: take a slice decomposition `T = ∑_j T_j` of length `S (T)`, each `T_j` a slice term
along its own leg `c_j`.  Distributing the external product gives `T ⊠ S = ∑_j (T_j ⊠ S)`, and
`T_j ⊠ S` is a sum of `1 · S_{c_j}(S) ≤ m` slice terms *along the single leg* `c_j`, by
submultiplicativity of the single-leg slice rank.  Subadditivity of slice rank over the list then
gives the bound `S (T) · m`. -/
theorem sliceRank_external_le_mul {m : ℕ} (T : Tensor3 K V) (S : Tensor3 K W)
    (h : ∀ c, sliceRankAlong c S ≤ m) :
    sliceRank (Tensor.external T S) ≤ sliceRank T * m := by
  obtain ⟨terms, hlen, hslice, hT⟩ := sliceRank_spec T
  have hexp : Tensor.external T S =
      ((terms.map Prod.snd).map fun A ↦ Tensor.external A S).sum := by
    rw [hT, external_list_sum_left]
  rw [sliceRank_le_iff, hexp]
  refine (SliceRankLE.list_sum (m := m) _ ?_).mono ?_
  · intro R hR
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hR
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hA
    have h1 : SliceRankAlongLE p.1 1 p.2 := (hslice p hp).sliceRankAlongLE
    have h2 : SliceRankAlongLE p.1 m S := sliceRankAlong_le_iff.mp (h p.1)
    exact ((h1.external h2).sliceRankLE).mono (Nat.le_of_eq (one_mul m))
  · simp only [List.length_map]
    exact Nat.mul_le_mul_right m hlen

/-- **Thesis Lemma 5.1(4)**, mirrored: if `S_c (T) ≤ m` for every leg `c`, then
`S (T ⊠ S) ≤ m · S (S)`. -/
theorem sliceRank_external_le_mul' {m : ℕ} (T : Tensor3 K V) (S : Tensor3 K W)
    (h : ∀ c, sliceRankAlong c T ≤ m) :
    sliceRank (Tensor.external T S) ≤ m * sliceRank S := by
  obtain ⟨terms, hlen, hslice, hS⟩ := sliceRank_spec S
  have hexp : Tensor.external T S =
      ((terms.map Prod.snd).map fun A ↦ Tensor.external T A).sum := by
    rw [hS, external_list_sum_right]
  rw [sliceRank_le_iff, hexp]
  refine (SliceRankLE.list_sum (m := m) _ ?_).mono ?_
  · intro R hR
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hR
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hA
    have h1 : SliceRankAlongLE p.1 m T := sliceRankAlong_le_iff.mp (h p.1)
    have h2 : SliceRankAlongLE p.1 1 p.2 := (hslice p hp).sliceRankAlongLE
    exact ((h1.external h2).sliceRankLE).mono (Nat.le_of_eq (mul_one m))
  · simp only [List.length_map]
    calc terms.length * m ≤ sliceRank S * m := Nat.mul_le_mul_right m hlen
      _ = m * sliceRank S := Nat.mul_comm _ _

/-- The largest of the three single-leg slice ranks, `max {S_x T, S_y T, S_z T}`.  It is the
quantity that controls products of slice ranks in thesis Lemma 5.1(4), and --- unlike slice rank
itself --- it is submultiplicative under external products. -/
noncomputable def maxSliceRankAlong (T : Tensor3 K V) : ℕ :=
  Finset.univ.sup fun c ↦ sliceRankAlong c T

/-- Each single-leg slice rank is bounded by their maximum. -/
theorem sliceRankAlong_le_maxSliceRankAlong (c : Leg) (T : Tensor3 K V) :
    sliceRankAlong c T ≤ maxSliceRankAlong T :=
  Finset.le_sup (f := fun d ↦ sliceRankAlong d T) (Finset.mem_univ c)

/-- The maximum of the single-leg slice ranks is bounded by `m` exactly when each of them is. -/
theorem maxSliceRankAlong_le_iff {T : Tensor3 K V} {m : ℕ} :
    maxSliceRankAlong T ≤ m ↔ ∀ c, sliceRankAlong c T ≤ m := by
  simp [maxSliceRankAlong, Finset.sup_le_iff]

/-- Slice rank is bounded by the largest single-leg slice rank. -/
theorem sliceRank_le_maxSliceRankAlong (T : Tensor3 K V) : sliceRank T ≤ maxSliceRankAlong T :=
  (sliceRank_le_sliceRankAlong Leg.X T).trans (sliceRankAlong_le_maxSliceRankAlong Leg.X T)

/-- The largest single-leg slice rank is bounded by ordinary tensor rank. -/
theorem maxSliceRankAlong_le_rank (T : Tensor3 K V) : maxSliceRankAlong T ≤ rank T :=
  maxSliceRankAlong_le_iff.mpr fun c ↦ sliceRankAlong_le_rank c T

/-- Restriction cannot increase the largest single-leg slice rank. -/
theorem maxSliceRankAlong_restricts_le {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) : maxSliceRankAlong S ≤ maxSliceRankAlong T :=
  maxSliceRankAlong_le_iff.mpr fun c ↦
    (sliceRankAlong_restricts_le h).trans (sliceRankAlong_le_maxSliceRankAlong c T)

/-- Legwise-isomorphic tensors have the same largest single-leg slice rank. -/
theorem maxSliceRankAlong_isomorphic {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Isomorphic T S) : maxSliceRankAlong T = maxSliceRankAlong S :=
  Finset.sup_congr rfl fun c _ ↦ sliceRankAlong_isomorphic (c := c) h

/-- **Submultiplicativity of the largest single-leg slice rank**, inherited legwise from
`sliceRankAlong_external_le`.  This is the estimate that bounds the slice ranks of all tensor
powers geometrically. -/
theorem maxSliceRankAlong_external_le (T : Tensor3 K V) (S : Tensor3 K W) :
    maxSliceRankAlong (Tensor.external T S) ≤ maxSliceRankAlong T * maxSliceRankAlong S :=
  maxSliceRankAlong_le_iff.mpr fun c ↦ (sliceRankAlong_external_le c T S).trans
    (Nat.mul_le_mul (sliceRankAlong_le_maxSliceRankAlong c T)
      (sliceRankAlong_le_maxSliceRankAlong c S))

/-- **Thesis Lemma 5.1(4)**: `S (A ⊠ B) ≤ S (A) · max {S_x B, S_y B, S_z B}`. -/
theorem sliceRank_external_le (T : Tensor3 K V) (S : Tensor3 K W) :
    sliceRank (Tensor.external T S) ≤ sliceRank T * maxSliceRankAlong S :=
  sliceRank_external_le_mul T S fun c ↦ sliceRankAlong_le_maxSliceRankAlong c S

/-- **Thesis Lemma 5.1(4)**, mirrored: `S (A ⊠ B) ≤ max {S_x A, S_y A, S_z A} · S (B)`. -/
theorem sliceRank_external_le' (T : Tensor3 K V) (S : Tensor3 K W) :
    sliceRank (Tensor.external T S) ≤ maxSliceRankAlong T * sliceRank S :=
  sliceRank_external_le_mul' T S fun c ↦ sliceRankAlong_le_maxSliceRankAlong c T

end SliceAlongSpan

section SliceAlongFinrank

variable {K : Type u} [Field K]
variable {V : Leg → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- **Thesis Lemma 5.1(5)**, dimension form: over a field, the leg-`c` slice rank of a tensor is
at most the dimension of its leg-`c` space. -/
theorem sliceRankAlong_le_finrank (c : Leg) [Module.Finite K (V c)] (T : Tensor3 K V) :
    sliceRankAlong c T ≤ Module.finrank K (V c) := by
  classical
  have hb := Module.finBasis K (V c)
  simpa using sliceRankAlong_le_card_of_span c hb (le_of_eq hb.span_eq.symm) T

/-- Over a field, slice rank is at most the dimension of each leg. -/
theorem sliceRank_le_finrank (c : Leg) [Module.Finite K (V c)] (T : Tensor3 K V) :
    sliceRank T ≤ Module.finrank K (V c) :=
  (sliceRank_le_sliceRankAlong c T).trans (sliceRankAlong_le_finrank c T)

end SliceAlongFinrank

/-! ## Slice subspaces -/

section SliceSubmodule

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable {W : Leg → Type w} [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- The subspace of tensors *sliced along `c` by `D`*: the span of the pure tensors whose leg-`c`
component lies in the subspace `D ≤ V c`.  In the classical notation for a three-legged tensor
space this is `D ⊗ Y ⊗ Z` for `c = X`, and its two rotations. -/
def sliceSubmodule (c : Leg) (D : Submodule K (V c)) : Submodule K (Tensor3 K V) :=
  Submodule.span K {t | ∃ x : ∀ i, V i, x c ∈ D ∧ t = pure (K := K) x}

/-- A pure tensor whose leg-`c` component lies in `D` lies in the slice subspace of `D`. -/
theorem pure_mem_sliceSubmodule {c : Leg} {D : Submodule K (V c)} {x : ∀ i, V i}
    (hx : x c ∈ D) : pure (K := K) x ∈ sliceSubmodule c D :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- Slice subspaces are monotone in the prescribed leg subspace. -/
theorem sliceSubmodule_mono {c : Leg} {D E : Submodule K (V c)} (h : D ≤ E) :
    sliceSubmodule (V := V) c D ≤ sliceSubmodule (V := V) c E :=
  Submodule.span_mono fun _ ⟨x, hx, hxt⟩ ↦ ⟨x, h hx, hxt⟩

/-- The image of any tensor under legwise linear maps is sliced along `c` by the range of the
leg-`c` map.  This is the only source of slice subspaces used below: a legwise map whose leg-`c`
component has small rank forces the image to have small leg-`c` slice rank. -/
theorem map_mem_sliceSubmodule (c : Leg) (f : ∀ i, V i →ₗ[K] W i) (T : Tensor3 K V) :
    Tensor.map f T ∈ sliceSubmodule c (LinearMap.range (f c)) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro r x
    rw [map_smul, map_pure]
    exact Submodule.smul_mem _ _ (pure_mem_sliceSubmodule ⟨x c, rfl⟩)
  · intro A B hA hB
    rw [map_add]
    exact Submodule.add_mem _ hA hB

/-- Slice terms with a prescribed leg-`c` vector are closed under scalar multiplication: the
scalar is absorbed into the leg `cycle c`, which is different from `c`, so the prescribed vector
is untouched. -/
theorem SliceTermWith.smul {c : Leg} {v : V c} {T : Tensor3 K V}
    (h : SliceTermWith c v T) (a : K) : SliceTermWith c v (a • T) := by
  rcases h with ⟨factors, hcomm, rfl⟩
  refine ⟨factors.map fun t ↦ Function.update t (cycle c) (a • t (cycle c)), ?_, ?_⟩
  · intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    rw [Function.update_of_ne (ne_cycle c)]
    exact hcomm t ht
  · rw [List.smul_sum, List.map_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t _ ↦ ?_)
    show a • pure (K := K) t =
      pure (K := K) (Function.update t (cycle c) (a • t (cycle c)))
    calc a • pure (K := K) t
        = a • pure (K := K) (Function.update t (cycle c) (t (cycle c))) := by
          rw [Function.update_eq_self]
      _ = pure (K := K) (Function.update t (cycle c) (a • t (cycle c))) :=
          ((PiTensorProduct.tprod K).map_update_smul t (cycle c) a (t (cycle c))).symm

/-- `SliceSumWith c e T` says that `T` splits into a family of slice terms indexed by `ι`, the
term at `i` carrying the prescribed leg-`c` vector `e i`.

Prescribing the vectors is what makes the predicate closed under addition and scalars: slice terms
along a common leg are not, but slice terms with a common *vector* are (`SliceTermWith.add`). -/
def SliceSumWith {ι : Type*} [Fintype ι] (c : Leg) (e : ι → V c) (T : Tensor3 K V) : Prop :=
  ∃ Ts : ι → Tensor3 K V, (∀ i, SliceTermWith c (e i) (Ts i)) ∧ T = ∑ i, Ts i

namespace SliceSumWith

variable {ι : Type*} [Fintype ι] {c : Leg} {e : ι → V c}

/-- The zero tensor splits into zero slice terms. -/
theorem zero : SliceSumWith (K := K) (V := V) c e (0 : Tensor3 K V) :=
  ⟨fun _ ↦ 0, fun i ↦ SliceTermWith.zero c (e i), by simp⟩

/-- Sums split termwise. -/
theorem add {T S : Tensor3 K V} (hT : SliceSumWith c e T) (hS : SliceSumWith c e S) :
    SliceSumWith c e (T + S) := by
  obtain ⟨Ts, hTs, rfl⟩ := hT
  obtain ⟨Ss, hSs, rfl⟩ := hS
  exact ⟨fun i ↦ Ts i + Ss i, fun i ↦ (hTs i).add (hSs i), (Finset.sum_add_distrib).symm⟩

/-- Scalar multiples split termwise. -/
theorem smul {T : Tensor3 K V} (hT : SliceSumWith c e T) (a : K) :
    SliceSumWith c e (a • T) := by
  obtain ⟨Ts, hTs, rfl⟩ := hT
  exact ⟨fun i ↦ a • Ts i, fun i ↦ (hTs i).smul a, Finset.smul_sum⟩

/-- A split family of slice terms is a leg-`c` slice certificate of length `Fintype.card ι`. -/
theorem sliceRankAlongLE {T : Tensor3 K V} (h : SliceSumWith c e T) :
    SliceRankAlongLE c (Fintype.card ι) T := by
  classical
  obtain ⟨Ts, hTs, rfl⟩ := h
  refine ⟨(Finset.univ : Finset ι).toList.map Ts, by simp, ?_, ?_⟩
  · intro S hS
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hS
    exact (hTs i).sliceTermAlong
  · rw [Finset.sum_map_toList]

end SliceSumWith

/-- Every tensor of the slice subspace spanned by a finite family `e` on leg `c` splits into one
slice term per family member.

Proof sketch: the predicate `SliceSumWith c e` is closed under zero, sums and scalars, and a pure
tensor whose leg-`c` component is a combination `∑ a i • e i` expands into the corresponding sum of
slice terms by `pure_eq_sum_update`.  Conclude by span induction. -/
theorem sliceSumWith_of_mem_sliceSubmodule {ι : Type*} [Fintype ι] (c : Leg) (e : ι → V c)
    {T : Tensor3 K V} (hT : T ∈ sliceSubmodule c (Submodule.span K (Set.range e))) :
    SliceSumWith c e T := by
  classical
  refine Submodule.span_induction (p := fun t _ ↦ SliceSumWith c e t) ?_ SliceSumWith.zero
    (fun _ _ _ _ hx hy ↦ hx.add hy) (fun a _ _ hx ↦ hx.smul a) hT
  rintro t ⟨x, hx, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
  refine ⟨fun i ↦ a i • pure (K := K) (Function.update x c (e i)), fun i ↦ ?_, ?_⟩
  · exact (SliceTermWith.pure_tensor _ (by simp)).smul (a i)
  · exact pure_eq_sum_update c e a x ha

/-- Tensors of the slice subspace spanned by a finite family have leg-`c` slice rank at most the
size of the family. -/
theorem sliceRankAlongLE_of_mem_sliceSubmodule {ι : Type*} [Fintype ι] (c : Leg) (e : ι → V c)
    {T : Tensor3 K V} (hT : T ∈ sliceSubmodule c (Submodule.span K (Set.range e))) :
    SliceRankAlongLE c (Fintype.card ι) T :=
  (sliceSumWith_of_mem_sliceSubmodule c e hT).sliceRankAlongLE

end SliceSubmodule

/-! ## The subspace characterization of slice rank -/

section SliceSubmoduleCharacterization

variable {K : Type u} [Field K]
variable {V : Leg → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- A slice term along `c` with slice vector `v` lies in the slice subspace of the line `K ∙ v`. -/
theorem SliceTermWith.mem_sliceSubmodule {c : Leg} {v : V c} {T : Tensor3 K V}
    (h : SliceTermWith c v T) : T ∈ sliceSubmodule c (Submodule.span K {v}) := by
  obtain ⟨factors, hcomm, rfl⟩ := h
  refine list_sum_mem fun t ht ↦ ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
  exact pure_mem_sliceSubmodule (by rw [hcomm x hx]; exact Submodule.mem_span_singleton_self v)

/-- Over a field, membership in the slice subspace of a finite-dimensional `D` bounds the leg-`c`
slice rank by `dim D`. -/
theorem sliceRankAlongLE_of_mem_sliceSubmodule_finrank (c : Leg) (D : Submodule K (V c))
    [Module.Finite K D] {T : Tensor3 K V} (hT : T ∈ sliceSubmodule c D) :
    SliceRankAlongLE c (Module.finrank K D) T := by
  classical
  set b := Module.finBasis K D with hbdef
  have hspan : Submodule.span K (Set.range fun i ↦ ((b i : D) : V c)) = D := by
    have himg : (Set.range fun i ↦ ((b i : D) : V c)) = D.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [himg, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  simpa using
    sliceRankAlongLE_of_mem_sliceSubmodule c (fun i ↦ ((b i : D) : V c)) (by rw [hspan]; exact hT)

/-- **Subspace bound for slice rank.**  A tensor lying in the sum of the three slice subspaces of
finite-dimensional leg subspaces has slice rank at most the total dimension. -/
theorem sliceRankLE_of_mem_sliceSubmodule_sup (D : ∀ c, Submodule K (V c))
    [∀ c, Module.Finite K (D c)] {T : Tensor3 K V}
    (hT : T ∈ sliceSubmodule Leg.X (D .X) ⊔ sliceSubmodule Leg.Y (D .Y) ⊔
      sliceSubmodule Leg.Z (D .Z)) :
    SliceRankLE (∑ c, Module.finrank K (D c)) T := by
  obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.mp hT
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp ha
  rw [sum_leg]
  exact (((sliceRankAlongLE_of_mem_sliceSubmodule_finrank _ _ hx).sliceRankLE).add
    ((sliceRankAlongLE_of_mem_sliceSubmodule_finrank _ _ hy).sliceRankLE)).add
    ((sliceRankAlongLE_of_mem_sliceSubmodule_finrank _ _ hz).sliceRankLE)

/-- Helper: the slice vectors of a slice certificate, collected leg by leg. -/
private theorem exists_sliceVector_lists (terms : List (Leg × Tensor3 K V))
    (hslice : ∀ p ∈ terms, SliceTermAlong p.1 p.2) :
    ∃ vs : ∀ c, List (V c), (∑ c, (vs c).length) ≤ terms.length ∧
      (terms.map Prod.snd).sum ∈
        sliceSubmodule Leg.X (Submodule.span K {v | v ∈ vs .X}) ⊔
          sliceSubmodule Leg.Y (Submodule.span K {v | v ∈ vs .Y}) ⊔
          sliceSubmodule Leg.Z (Submodule.span K {v | v ∈ vs .Z}) := by
  classical
  induction terms with
  | nil =>
      refine ⟨fun _ ↦ [], by simp, ?_⟩
      simp
  | cons pr rest ih =>
      obtain ⟨c, S⟩ := pr
      obtain ⟨vs', hlen', hmem'⟩ := ih fun q hq ↦ hslice q (List.mem_cons_of_mem _ hq)
      obtain ⟨v, hv⟩ := (hslice (c, S) (List.mem_cons_self ..)).exists_sliceTermWith
      refine ⟨Function.update vs' c (v :: vs' c), ?_, ?_⟩
      · rw [sum_leg]
        rw [sum_leg] at hlen'
        cases c with
        | X =>
            rw [Function.update_self, Function.update_of_ne (by decide : Leg.Y ≠ Leg.X),
              Function.update_of_ne (by decide : Leg.Z ≠ Leg.X)]
            simp only [List.length_cons]
            omega
        | Y =>
            rw [Function.update_self, Function.update_of_ne (by decide : Leg.X ≠ Leg.Y),
              Function.update_of_ne (by decide : Leg.Z ≠ Leg.Y)]
            simp only [List.length_cons]
            omega
        | Z =>
            rw [Function.update_self, Function.update_of_ne (by decide : Leg.X ≠ Leg.Z),
              Function.update_of_ne (by decide : Leg.Y ≠ Leg.Z)]
            simp only [List.length_cons]
            omega
      · have hgrow : ∀ i : Leg, ({u | u ∈ vs' i} : Set (V i)) ⊆
            {u | u ∈ Function.update vs' c (v :: vs' c) i} := by
          intro i u hu
          by_cases hi : i = c
          · subst hi
            rw [Function.update_self]
            exact List.mem_cons_of_mem _ hu
          · rwa [Function.update_of_ne hi]
        have hmono : ∀ i : Leg,
            sliceSubmodule i (Submodule.span K {u | u ∈ vs' i}) ≤
              sliceSubmodule i (Submodule.span K {u | u ∈ Function.update vs' c (v :: vs' c) i}) :=
          fun i ↦ sliceSubmodule_mono (Submodule.span_mono (hgrow i))
        have hS : S ∈ sliceSubmodule c
            (Submodule.span K {u | u ∈ Function.update vs' c (v :: vs' c) c}) := by
          refine sliceSubmodule_mono (Submodule.span_mono ?_) hv.mem_sliceSubmodule
          intro u hu
          rw [Set.mem_singleton_iff] at hu
          subst hu
          rw [Function.update_self]
          exact List.mem_cons_self ..
        rw [List.map_cons, List.sum_cons]
        refine Submodule.add_mem _ ?_ ?_
        · cases c with
          | X => exact Submodule.mem_sup_left (Submodule.mem_sup_left hS)
          | Y => exact Submodule.mem_sup_left (Submodule.mem_sup_right hS)
          | Z => exact Submodule.mem_sup_right hS
        · have hle : sliceSubmodule Leg.X (Submodule.span K {u | u ∈ vs' .X}) ⊔
              sliceSubmodule Leg.Y (Submodule.span K {u | u ∈ vs' .Y}) ⊔
              sliceSubmodule Leg.Z (Submodule.span K {u | u ∈ vs' .Z}) ≤
              sliceSubmodule Leg.X
                  (Submodule.span K {u | u ∈ Function.update vs' c (v :: vs' c) .X}) ⊔
                sliceSubmodule Leg.Y
                  (Submodule.span K {u | u ∈ Function.update vs' c (v :: vs' c) .Y}) ⊔
                sliceSubmodule Leg.Z
                  (Submodule.span K {u | u ∈ Function.update vs' c (v :: vs' c) .Z}) :=
            sup_le (sup_le ((hmono Leg.X).trans (le_trans le_sup_left le_sup_left))
              ((hmono Leg.Y).trans (le_trans le_sup_right le_sup_left)))
              ((hmono Leg.Z).trans le_sup_right)
          exact hle hmem'

/-- **Subspace characterization of slice rank** over a field.  A tensor has slice rank at most `r`
exactly when it lies in `A ⊗ Y ⊗ Z + X ⊗ B ⊗ Z + X ⊗ Y ⊗ C` for leg subspaces of total dimension at
most `r`.

The finiteness hypothesis is on the *subspaces*, not on the leg spaces: the forward direction
produces spans of finitely many slice vectors, which are automatically finite-dimensional, and the
backward direction only needs a finite basis of each subspace.  No finiteness of `V c` is forced. -/
theorem sliceRankLE_iff_exists_sliceSubmodules {r : ℕ} {T : Tensor3 K V} :
    SliceRankLE r T ↔
      ∃ D : ∀ c, Submodule K (V c), ∃ _ : ∀ c, Module.Finite K (D c),
        (∑ c, Module.finrank K (D c)) ≤ r ∧
        T ∈ sliceSubmodule Leg.X (D .X) ⊔ sliceSubmodule Leg.Y (D .Y) ⊔
          sliceSubmodule Leg.Z (D .Z) := by
  classical
  constructor
  · rintro ⟨terms, hlen, hslice, rfl⟩
    obtain ⟨vs, hvlen, hmem⟩ := exists_sliceVector_lists terms hslice
    have hset : ∀ c : Leg, ({u | u ∈ vs c} : Set (V c)) = ((vs c).toFinset : Set (V c)) := by
      intro c
      simp [List.coe_toFinset]
    simp only [hset] at hmem
    refine ⟨fun c ↦ Submodule.span K ((vs c).toFinset : Set (V c)), fun _ ↦ inferInstance,
      ?_, hmem⟩
    refine le_trans (Finset.sum_le_sum fun c _ ↦ ?_) (le_trans hvlen hlen)
    exact (finrank_span_finset_le_card _).trans (List.toFinset_card_le _)
  · rintro ⟨D, _, hdim, hmem⟩
    exact (sliceRankLE_of_mem_sliceSubmodule_sup D hmem).mono hdim

end SliceSubmoduleCharacterization

end AlgebraicComplexity.Tensor
