/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/
import AlgebraicComplexity.MatrixMultiplication.IndependenceBarrier
import AlgebraicComplexity.MatrixMultiplication.IndependentDiagonal
import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerHashing
import AlgebraicComplexity.Tensor.CoordinateBlockWord

/-!
# Coordinate block certificates: block tables whose blocks are matrix-multiplication pullbacks

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module is the paper-independent core
shared by the coordinate ("shadow") extractions of the barrier program of
[AlmanVassilevskaWilliams2018]: a coefficient table whose variables carry a *block label* on each
leg and whose block sub-tables are, in the listed coordinates, coefficient tables of
matrix-multiplication tensors.  For such a table every finite set of selected *block words*
produced by a hashing pipeline is automatically a
`AlgebraicComplexity.CoordinateGalacticCertificate`.

## The data

`BlockMMIndexing κ A S` records, for variable alphabets `κ` and block alphabets `A`:

* a block labelling `label i : κ i → A i` of the variables of each leg;
* a finite family of *constituents* indexed by `S`, each with a block address
  `letter s : BlockAddress A` and matrix dimensions `dimM s`, `dimN s`, `dimP s`;
* legwise bijections `index s c` between the variables of leg `c` of
  `⟨dimM s, dimN s, dimP s⟩` and the variables of leg `c` carrying the block label `letter s c`.

The coefficient table itself is *not* part of the structure: the index bijections are
coefficient-free, so the same indexing serves every coefficient ring.  The property tying a table
to the indexing is `BlockMMIndexing.IsBlockTable`, the **letter identity**: read along `index s`,
the table is `AlgebraicComplexity.mmCoefficients` of the constituent's shape.

## Main definitions

* `BlockMMIndexing.wordIndex D w c v`: the coordinates of leg `c` of the constituent selected by a
  word `w : Fin N → S` of constituents, listed position by position.
* `BlockMMIndexing.constituentIndex D w hm hn hp c u`: the same coordinates compressed by the
  mixed-radix digit bijection `AlgebraicComplexity.mmWordIndexEquiv` into a single index of
  `⟨a, b, d⟩`, where `a`, `b`, `d` are the three dimension products along the word.

## Main results

* `BlockMMIndexing.coordinatePower_wordIndex`: **the word identity.**  The constituent selected by
  a word of constituents is the heterogeneous word product
  `AlgebraicComplexity.mmWordCoefficients` of the constituents' shapes.
* `BlockMMIndexing.coordinatePower_constituentIndex`: **the constituent identity.**  After the
  mixed-radix compression it is `mmCoefficients K a b d`.
* `BlockMMIndexing.exists_zeroOut_eq_extend`: **the assembly.**  Given an enumeration `key` of
  selected block words, each of which is the block word of a word `w j` of constituents with fixed
  dimension products `a`, `b`, `d`, legwise injective and cut out from the support of the power by
  legwise sets `BW` of block words, the Kronecker power of the table *zeroes out* to `copies`
  disjoint copies of `⟨a, b, d⟩`.
* `BlockMMIndexing.coordinateGalacticCertificate`: the same, packaged through
  `AlgebraicComplexity.coordinateGalacticCertificate_of_zeroOut`.

Both hypotheses of the assembly are exactly what a legwise hashing pipeline delivers: `hkeyinj` is
`Tensor.IsLegwiseInjective` of the selected addresses, and `hclosed` is the coordinate form of
projection closedness relative to the support of the power, which for the AVW clients comes from
`Tensor.HasUniqueLegFibers` on one leg.

## Universes

All three alphabets live in `Type 0`.  This is forced by `Tensor/CoordinateBlockWord.lean`, whose
block-table theorem puts the variable alphabet, the block alphabet and the *constituent* variable
alphabet in one universe, and the latter is `Fin F × MMIndex a b d i`, a `Type 0`.  A `ULift` of
the block alphabet there would remove the restriction.

## Position in the library

Layer 3.  It imports `MatrixMultiplication/IndependenceBarrier.lean` (for the certificate and its
zeroing-out constructor), `MatrixMultiplication/IndependentDiagonal.lean` (for `mmCoefficients`
and the heterogeneous word bijections) and `Tensor/CoordinateBlockWord.lean` (for the block-word
calculus).  It mentions no named tensor and no numerical bound.

## References

* [AlmanVassilevskaWilliams2018] J. Alman and V. Vassilevska Williams, *Limits on all known (and
  some unknown) approaches to matrix multiplication*, arXiv:1810.08671; Lemma 4.4, Theorem 7.3.
-/

namespace AlgebraicComplexity

open Tensor

universe u

/-- **The block words of the support of a Kronecker power are support words.**  If a table
vanishes at every variable triple whose block address is unsupported, then a triple of length
`n + 1` words with a nonzero coefficient in `Tensor.coordinatePower T (n + 1)` carries a supported
block address at every position, so its triple of legwise block words is the block address of a
word of supported addresses in the sense of
`AlgebraicComplexity.PartitionHashEncoding.supportWordAddress`.

This is the coordinate entry point of the hashing pipeline: it is what lets a client conclude that
a surviving triple of the power lies in the *full* modeled family, which the hash filter then
intersects. -/
theorem exists_blockSupportWord_of_coordinatePower_ne_zero {K : Type u} [CommSemiring K]
    {κ A : Leg → Type} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) (support : Finset (BlockAddress A))
    (hzero : ∀ s : ∀ i, κ i, (fun c ↦ blk c (s c)) ∉ support → T s = 0)
    (n : ℕ) {p : ∀ c, Fin (n + 1) → κ c} (hp : coordinatePower T (n + 1) p ≠ 0) :
    ∃ word : PositiveWord support n,
      blockAddressWordEquiv A n
          (PartitionHashEncoding.supportWordAddress (A := A) (support := support) n word)
        = coordinateBlockWord blk p := by
  have hmem : ∀ t, (fun c ↦ blk c (p c t)) ∈ support := by
    intro t
    by_contra hno
    exact hp (Finset.prod_eq_zero (Finset.mem_univ t) (hzero _ hno))
  refine ⟨(positiveWordEquiv support n).symm fun t ↦ ⟨_, hmem t⟩, ?_⟩
  funext c
  have h := PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := A) (support := support) n ((positiveWordEquiv support n).symm fun t ↦ ⟨_, hmem t⟩) c
  rw [blockAddressWordEquiv_apply, h]
  funext t
  simp [coordinateBlockWord, coordinateBlockLegWord]

/-- **A block indexing of a coordinate table by matrix-multiplication constituents.**

`label i` is the block labelling of the variables of leg `i`; the constituents are indexed by `S`,
the constituent `s` occupies the block address `letter s` and has matrix-multiplication shape
`⟨dimM s, dimN s, dimP s⟩`, and `index s c` lists the variables of leg `c` of that shape by
variables of leg `c` of the ambient table carrying the block label `letter s c`.

The coefficient table is deliberately absent: see `BlockMMIndexing.IsBlockTable`. -/
structure BlockMMIndexing (κ A : Leg → Type) (S : Type) where
  /-- The block label of a variable of leg `i`. -/
  label : ∀ i, κ i → A i
  /-- The block address occupied by the constituent `s`. -/
  letter : S → BlockAddress A
  /-- First matrix dimension of the constituent `s`. -/
  dimM : S → ℕ
  /-- Second matrix dimension of the constituent `s`. -/
  dimN : S → ℕ
  /-- Third matrix dimension of the constituent `s`. -/
  dimP : S → ℕ
  /-- The variables of leg `c` of the constituent `s`, listed inside the ambient leg. -/
  index : ∀ (s : S) (c : Leg),
    MMIndex (dimM s) (dimN s) (dimP s) c ≃ {x : κ c // label c x = letter s c}

namespace BlockMMIndexing

variable {κ A : Leg → Type} {S : Type} (D : BlockMMIndexing κ A S)

/-- **The letter identity.**  A coefficient table `T` is a block table for the indexing `D` when,
read along the coordinates listed by `index s`, its block at the address `letter s` is the
coefficient table of the matrix-multiplication tensor `⟨dimM s, dimN s, dimP s⟩`. -/
def IsBlockTable {K : Type u} [CommSemiring K] (T : (∀ i, κ i) → K) : Prop :=
  ∀ (s : S) (u : ∀ c, MMIndex (D.dimM s) (D.dimN s) (D.dimP s) c),
    T (fun c ↦ (D.index s c (u c) : κ c)) = mmCoefficients K (D.dimM s) (D.dimN s) (D.dimP s) u

section Word

variable {N : ℕ}

/-- **The coordinates of leg `c` of the constituent selected by a word of constituents.**  Position
by position it is the letter listing `index`. -/
def wordIndex (w : Fin N → S) (c : Leg)
    (v : ∀ t, MMIndex (D.dimM (w t)) (D.dimN (w t)) (D.dimP (w t)) c) : Fin N → κ c :=
  fun t ↦ (D.index (w t) c (v t) : κ c)

/-- A listed coordinate of a constituent carries the block label prescribed by its block word. -/
@[simp] theorem label_wordIndex (w : Fin N → S) (c : Leg)
    (v : ∀ t, MMIndex (D.dimM (w t)) (D.dimN (w t)) (D.dimP (w t)) c) (t : Fin N) :
    D.label c (D.wordIndex w c v t) = D.letter (w t) c :=
  (D.index (w t) c (v t)).2

/-- The listed coordinates of a constituent form the prescribed block word. -/
theorem coordinateBlockLegWord_wordIndex (w : Fin N → S) (c : Leg)
    (v : ∀ t, MMIndex (D.dimM (w t)) (D.dimN (w t)) (D.dimP (w t)) c) :
    coordinateBlockLegWord D.label c (D.wordIndex w c v) = fun t ↦ D.letter (w t) c := by
  funext t
  exact D.label_wordIndex w c v t

/-- Distinct coordinates of a constituent are listed by distinct indices. -/
theorem wordIndex_injective (w : Fin N → S) (c : Leg) :
    Function.Injective (D.wordIndex w c) := by
  intro v v' h
  funext t
  refine (D.index (w t) c).injective (Subtype.ext ?_)
  exact congrFun h t

/-- Every coordinate word with the prescribed block word is listed by the constituent. -/
theorem exists_wordIndex (w : Fin N → S) (c : Leg) {x : Fin N → κ c}
    (hx : ∀ t, D.label c (x t) = D.letter (w t) c) :
    ∃ v, D.wordIndex w c v = x := by
  refine ⟨fun t ↦ (D.index (w t) c).symm ⟨x t, hx t⟩, ?_⟩
  funext t
  simp [wordIndex]

/-- **The word identity.**  The constituent selected by a word of constituents is the heterogeneous
word product of the constituents' matrix-multiplication shapes.  It is the letter identity
multiplied over the `N` positions. -/
theorem coordinatePower_wordIndex {K : Type u} [CommSemiring K] {T : (∀ i, κ i) → K}
    (hT : D.IsBlockTable T) (w : Fin N → S)
    (v : ∀ c, ∀ t, MMIndex (D.dimM (w t)) (D.dimN (w t)) (D.dimP (w t)) c) :
    coordinatePower T N (fun c ↦ D.wordIndex w c (v c))
      = mmWordCoefficients K (fun t ↦ D.dimM (w t)) (fun t ↦ D.dimN (w t))
          (fun t ↦ D.dimP (w t)) v := by
  rw [coordinatePower_apply, mmWordCoefficients_apply]
  exact Finset.prod_congr rfl fun t _ ↦ hT (w t) fun c ↦ v c t

/-- **The coordinates of one constituent, compressed to a single matrix-multiplication shape.**
The mixed-radix digit bijection `AlgebraicComplexity.mmWordIndexEquiv` turns a word of indices of
the constituents' shapes into one index of `⟨a, b, d⟩`, where `a`, `b` and `d` are the products of
the three dimension words. -/
noncomputable def constituentIndex (w : Fin N → S) {a b d : ℕ}
    (hm : ∏ t, D.dimM (w t) = a) (hn : ∏ t, D.dimN (w t) = b) (hp : ∏ t, D.dimP (w t) = d)
    (c : Leg) (u : MMIndex a b d c) : Fin N → κ c :=
  D.wordIndex w c
    ((mmWordIndexEquiv (fun t ↦ D.dimM (w t)) (fun t ↦ D.dimN (w t))
        (fun t ↦ D.dimP (w t)) c).symm (mmIndexCongr hm.symm hn.symm hp.symm c u))

/-- **The constituent identity.**  Read along the compressed coordinates, the `N`-th Kronecker
power of a block table is the coefficient table of `⟨a, b, d⟩`. -/
theorem coordinatePower_constituentIndex {K : Type u} [CommSemiring K] {T : (∀ i, κ i) → K}
    (hT : D.IsBlockTable T) (w : Fin N → S) {a b d : ℕ}
    (hm : ∏ t, D.dimM (w t) = a) (hn : ∏ t, D.dimN (w t) = b) (hp : ∏ t, D.dimP (w t) = d)
    (u : ∀ c, MMIndex a b d c) :
    coordinatePower T N (fun c ↦ D.constituentIndex w hm hn hp c (u c))
      = mmCoefficients K a b d u := by
  simp only [constituentIndex]
  rw [D.coordinatePower_wordIndex hT]
  have hrel := congrFun (coordinateRelabel_mmWordIndexEquiv K
      (fun t ↦ D.dimM (w t)) (fun t ↦ D.dimN (w t)) (fun t ↦ D.dimP (w t)))
    (fun c ↦ mmIndexCongr hm.symm hn.symm hp.symm c (u c))
  rw [coordinateRelabel_apply] at hrel
  rw [hrel]
  exact mmCoefficients_mmIndexCongr hm.symm hn.symm hp.symm u

/-- The compressed coordinates of a constituent are still listed injectively. -/
theorem constituentIndex_injective (w : Fin N → S) {a b d : ℕ}
    (hm : ∏ t, D.dimM (w t) = a) (hn : ∏ t, D.dimN (w t) = b) (hp : ∏ t, D.dimP (w t) = d)
    (c : Leg) :
    Function.Injective (D.constituentIndex w hm hn hp c) :=
  ((D.wordIndex_injective w c).comp (Equiv.injective _)).comp (Equiv.injective _)

/-- The compressed coordinates of a constituent form the prescribed block word. -/
theorem coordinateBlockLegWord_constituentIndex (w : Fin N → S) {a b d : ℕ}
    (hm : ∏ t, D.dimM (w t) = a) (hn : ∏ t, D.dimN (w t) = b) (hp : ∏ t, D.dimP (w t) = d)
    (c : Leg) (u : MMIndex a b d c) :
    coordinateBlockLegWord D.label c (D.constituentIndex w hm hn hp c u)
      = fun t ↦ D.letter (w t) c :=
  D.coordinateBlockLegWord_wordIndex w c _

/-- Every coordinate word with the prescribed block word is listed by the compressed
constituent. -/
theorem exists_constituentIndex (w : Fin N → S) {a b d : ℕ}
    (hm : ∏ t, D.dimM (w t) = a) (hn : ∏ t, D.dimN (w t) = b) (hp : ∏ t, D.dimP (w t) = d)
    (c : Leg) {x : Fin N → κ c} (hx : ∀ t, D.label c (x t) = D.letter (w t) c) :
    ∃ u, D.constituentIndex w hm hn hp c u = x := by
  obtain ⟨v, hv⟩ := D.exists_wordIndex w c hx
  refine ⟨(mmIndexCongr hm.symm hn.symm hp.symm c).symm
      (mmWordIndexEquiv (fun t ↦ D.dimM (w t)) (fun t ↦ D.dimN (w t))
        (fun t ↦ D.dimP (w t)) c v), ?_⟩
  rw [constituentIndex]
  simpa using hv

end Word

section Assembly

variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable [∀ i, DecidableEq (A i)]
variable {K : Type u} [CommSemiring K] {T : (∀ i, κ i) → K}

/-- **The assembly: a family of selected block words is a zeroing out onto disjoint copies of one
matrix-multiplication tensor.**

`key` enumerates the selected block words; `w j` is the word of constituents realizing `key j`
(`hletter`), whose three dimension products are the common `a`, `b`, `d` (`hm`, `hn`, `hp`).  The
two combinatorial hypotheses are the coordinate forms of the abstract extraction chain:

* `hkeyinj` is legwise injectivity of the selected block words, which makes the legwise variable
  listings of the different copies disjoint;
* `hclosed` says that a *support* triple of the power whose three legwise block words are selected
  by the legwise sets `BW` already has a selected block word, so zeroing out at the legwise fibers
  of `BW` gains no cross term.

Proof sketch.  The legwise variable listings are `constituentIndex`, which are injective
(`constituentIndex_injective`), carry the prescribed block words
(`coordinateBlockLegWord_constituentIndex`) and cover every word with such a block word
(`exists_constituentIndex`); `Function.invFun` supplies the retractions.  The block zeroing out at
the image of `key` is a zeroing out at the legwise fibers of `BW`
(`Tensor.coordinateBlockZeroOut_eq_coordinateZeroOut`, whose two hypotheses are `hsub` and
`hclosed`), and it is a block table of its constituents
(`Tensor.coordinateBlockZeroOut_eq_extend_directSum`, whose hypotheses are the three properties of
the listings).  Each constituent is `mmCoefficients K a b d` by
`coordinatePower_constituentIndex`. -/
theorem exists_zeroOut_eq_extend (hT : D.IsBlockTable T) {N a b d copies : ℕ}
    (key : Fin copies → BlockAddress fun i ↦ Fin N → A i) (w : Fin copies → Fin N → S)
    (hletter : ∀ (j : Fin copies) (c : Leg) (t : Fin N), key j c t = D.letter (w j t) c)
    (hkeyinj : ∀ i, Function.Injective fun j ↦ key j i)
    (hm : ∀ j, ∏ t, D.dimM (w j t) = a) (hn : ∀ j, ∏ t, D.dimN (w j t) = b)
    (hp : ∀ j, ∏ t, D.dimP (w j t) = d)
    (hcopies : 0 < copies) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (BW : ∀ i, Finset (Fin N → A i)) (hsub : ∀ (j : Fin copies) (i : Leg), key j i ∈ BW i)
    (hclosed : ∀ p : ∀ i, Fin N → κ i, coordinatePower T N p ≠ 0 →
      (∀ i, coordinateBlockWord D.label p i ∈ BW i) →
      ∃ j, coordinateBlockWord D.label p = key j) :
    ∃ (Z : ∀ i, Finset (Fin N → κ i))
      (f : ∀ i, Fin copies × MMIndex a b d i → (Fin N → κ i))
      (g : ∀ i, (Fin N → κ i) → Fin copies × MMIndex a b d i),
      (∀ i x, g i (f i x) = x) ∧
        coordinateZeroOut (coordinatePower T N) Z =
          coordinateExtend f g (coordinateDirectSum fun _ : Fin copies ↦
            mmCoefficients K a b d) := by
  classical
  set Sel : Finset (BlockAddress fun i ↦ Fin N → A i) := Finset.image key Finset.univ with hSeldef
  have hmemS : ∀ j, key j ∈ Sel := fun j ↦ Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hsurjS : ∀ s ∈ Sel, ∃ j, key j = s := by
    intro s hs
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hs
    exact ⟨j, hj⟩
  -- The legwise listing of the variables of the selected constituents.
  set f : ∀ i, Fin copies × MMIndex a b d i → (Fin N → κ i) :=
    fun i x ↦ D.constituentIndex (w x.1) (hm x.1) (hn x.1) (hp x.1) i x.2 with hfdef
  have hfval : ∀ i j x, f i (j, x)
      = D.constituentIndex (w j) (hm j) (hn j) (hp j) i x := fun _ _ _ ↦ rfl
  have hfblock : ∀ i j x,
      coordinateBlockLegWord D.label i (f i (j, x)) = key j i := by
    intro i j x
    rw [hfval, D.coordinateBlockLegWord_constituentIndex]
    funext t
    exact (hletter j i t).symm
  have hfinj : ∀ i, Function.Injective (f i) := by
    rintro i ⟨j, x⟩ ⟨j', x'⟩ h
    have hb : key j i = key j' i := by rw [← hfblock i j x, ← hfblock i j' x', h]
    have hj : j = j' := hkeyinj i hb
    subst hj
    rw [hfval, hfval] at h
    rw [D.constituentIndex_injective (w j) (hm j) (hn j) (hp j) i h]
  have hnonempty : ∀ i : Leg, Nonempty (Fin copies × MMIndex a b d i) := by
    intro i
    exact ⟨(⟨0, hcopies⟩, by cases i <;> exact (⟨0, by omega⟩, ⟨0, by omega⟩))⟩
  set g : ∀ i, (Fin N → κ i) → Fin copies × MMIndex a b d i :=
    fun i ↦ @Function.invFun _ _ (hnonempty i) (f i) with hgdef
  have hgf : ∀ i x, g i (f i x) = x := by
    intro i x
    rw [hgdef]
    exact @Function.leftInverse_invFun _ _ (hnonempty i) _ (hfinj i) x
  have hcover : ∀ (i : Leg) (v : Fin N → κ i),
      (∃ j, key j i = coordinateBlockLegWord D.label i v) → f i (g i v) = v := by
    rintro i v ⟨j, hj⟩
    have hx : ∀ t, D.label i (v t) = D.letter (w j t) i := by
      intro t
      have ht := congrFun hj t
      rw [hletter j i t] at ht
      exact ht.symm
    obtain ⟨u, hu⟩ := D.exists_constituentIndex (w j) (hm j) (hn j) (hp j) i hx
    rw [hgdef]
    exact @Function.invFun_eq _ _ (hnonempty i) (f i) v ⟨(j, u), by rw [hfval]; exact hu⟩
  refine ⟨fun i ↦ coordinateBlockFiber D.label i (BW i), f, g, hgf, ?_⟩
  have hconst : (fun j ↦ coordinateBlockWordConstituent T D.label
        (fun i x ↦ f i (j, x)) (key j))
      = fun _ : Fin copies ↦ mmCoefficients K a b d := by
    funext j
    rw [coordinateBlockWordConstituent_eq_coordinatePower _ _ fun i x ↦ hfblock i j x]
    funext v
    rw [show (fun i ↦ f i (j, v i)) = fun i ↦
        D.constituentIndex (w j) (hm j) (hn j) (hp j) i (v i) from
      funext fun i ↦ hfval i j (v i)]
    exact D.coordinatePower_constituentIndex hT (w j) (hm j) (hn j) (hp j) v
  rw [← coordinateBlockZeroOut_eq_coordinateZeroOut T D.label Sel BW
      (fun s hs i ↦ by obtain ⟨j, hj⟩ := hsurjS s hs; exact hj ▸ hsub j i)
      (fun p hp' hmem ↦ by obtain ⟨j, hj⟩ := hclosed p hp' hmem; exact hj ▸ hmemS j),
    coordinateBlockZeroOut_eq_extend_directSum T D.label hmemS hsurjS hkeyinj hfblock hcover,
    hconst]

/-- **The packaged certificate.**  Milestone M2
(`AlgebraicComplexity.coordinateGalacticCertificate_of_zeroOut`) turns the zeroing out of
`BlockMMIndexing.exists_zeroOut_eq_extend` into a coordinate galactic certificate, with the
indicator weights `w i v = if v ∈ Z i then 0 else 1` and threshold `0`. -/
theorem coordinateGalacticCertificate (hT : D.IsBlockTable T) {N a b d copies : ℕ}
    (key : Fin copies → BlockAddress fun i ↦ Fin N → A i) (w : Fin copies → Fin N → S)
    (hletter : ∀ (j : Fin copies) (c : Leg) (t : Fin N), key j c t = D.letter (w j t) c)
    (hkeyinj : ∀ i, Function.Injective fun j ↦ key j i)
    (hm : ∀ j, ∏ t, D.dimM (w j t) = a) (hn : ∀ j, ∏ t, D.dimN (w j t) = b)
    (hp : ∀ j, ∏ t, D.dimP (w j t) = d)
    (hcopies : 0 < copies) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (BW : ∀ i, Finset (Fin N → A i)) (hsub : ∀ (j : Fin copies) (i : Leg), key j i ∈ BW i)
    (hclosed : ∀ p : ∀ i, Fin N → κ i, coordinatePower T N p ≠ 0 →
      (∀ i, coordinateBlockWord D.label p i ∈ BW i) →
      ∃ j, coordinateBlockWord D.label p = key j) :
    CoordinateGalacticCertificate K T N a b d copies := by
  obtain ⟨Z, f, g, hgf, heq⟩ :=
    D.exists_zeroOut_eq_extend hT key w hletter hkeyinj hm hn hp hcopies ha hb hd BW hsub hclosed
  exact coordinateGalacticCertificate_of_zeroOut K Z f g hgf heq

end Assembly

end BlockMMIndexing

end AlgebraicComplexity
