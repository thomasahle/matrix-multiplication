/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.Tensor.PartitionedRelabeling
import AlgebraicComplexity.Tensor.PartitionedPowerRelabeling

/-!
# Single-leg hole repair

Layer 1 (`AlgebraicComplexity/Tensor/`).  This module formalizes the tensor-level content of the
Hole Lemma of

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§5 (`hole_lemma.tex`), Lemma 5.3 and Corollary 5.4**
> (`[DuanWuZhou2022]`).

## What the paper's lemma is, and why it is *not* the repair already in this library

`Tensor/HoleRepair.lean` and `Tensor/HoleRepairTree.lean` implement the
Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou repair: holes may sit on **all three** legs, an
intact box is reassembled from an eight-box decomposition, and the recursion costs `7^height`
broken copies.

`[DuanWuZhou2022]` repair a strictly easier situation and pay only `O(n)`.  Their broken copies
have holes on **one leg only** (Z).  The decisive consequence is combinatorial rather than
algebraic: when a hole is a single leg-`c₀` block label, a supported block address is destroyed
precisely when *its own* `c₀`-label is a hole, so "every address survives somewhere" reduces to
"every leg-`c₀` label survives somewhere".  That is a union bound over one leg's alphabet, not a
condition coupling three legs inside one copy — which is exactly what forces the seven-branch
recursion in the three-leg case.

Once the covering statement is available the repair itself is short, and this module proves it in
its sharpest form: no group action, no probability, no counting.  The caller supplies a function
`choose` naming, for each leg-`c₀` label, one copy in which that label is not a hole; the
conclusion is a genuine `Restricts` chain — additional block zeroing followed by the
identification degeneration `⊕ᵢ Tᵢ ⊵ ∑ᵢ Tᵢ` (`Restricts.indexedDirectSum_to_sum`) — never an
assumed relation.

## Principal results

* `Tensor.legKeep` — the leg-local keep predicate constraining only one tensor leg, with
  `legKeep_iff` reducing "the whole address survives" to "its `c₀`-label survives".
* `PartitionedTensor.holeSelect` — the broken copy: `P` with every block whose leg-`c₀` label is a
  hole zeroed out.  This is `[DuanWuZhou2022]`'s *broken copy of a standard form tensor*
  (Definition 5.2) once the standard form tensor itself is supplied by the caller.
* `PartitionedTensor.StructureRelabeling.holeSelect_reindex_eq` and `holeSelect_isomorphic` — a
  structure-preserving relabeling of `P` carries a broken copy to the copy with *moved* holes.
  This is the tensor-level content of the paper's shuffling step: shuffling a broken copy is an
  isomorphism, and it transports the hole set by the relabeling.
* `Tensor.Restricts.indexedDirectSum_legHoleRepair` — **the Hole Lemma**: if every supported
  address has a copy in which its leg-`c₀` label is not a hole, then the direct sum of the broken
  copies restricts onto the intact `P`.
* `Tensor.Restricts.indexedDirectSum_shuffledLegHoleRepair` — the same statement with one
  structure relabeling per copy, i.e. `[DuanWuZhou2022]`'s displayed form
  `⊕_t 𝒯'_t ⊵ 𝒯^*` after shuffling.

The counting that produces `choose` from a fraction of surviving holes is deliberately *not* here:
it is finite combinatorics over one alphabet and belongs to
`Combinatorics/ShufflingGroup.lean`, one layer up.

## Non-goals

The paper's `s' = ⌊∑ η / (Nℓ + 2)⌋` corollary (Corollary 5.4) is a statement about grouping the
broken copies into blocks and applying the lemma once per block.  It is a client-side arithmetic
packaging of the theorem proved here and is not repeated at this layer.
-/

namespace AlgebraicComplexity.Tensor

open scoped BigOperators

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-! ## Leg-local selections -/

/-- **The leg-local keep predicate.**  `legKeep c₀ keepAt` constrains only the leg `c₀`, where it
is `keepAt`; the other two legs are unconstrained.

`[DuanWuZhou2022]`'s holes live only in Z, so every selection in their Hole Lemma has this
shape. -/
def legKeep (c₀ : Leg) (keepAt : A c₀ → Prop) : ∀ c, A c → Prop :=
  fun c ↦ if h : c₀ = c then h ▸ keepAt else fun _ ↦ True

/-- Decidability of a leg-local predicate.  Classical, matching the rest of the partitioned-tensor
selection API: the object is noncomputable anyway. -/
noncomputable instance decidableLegKeep (c₀ : Leg) (keepAt : A c₀ → Prop)
    (c : Leg) (a : A c) : Decidable (legKeep (A := A) c₀ keepAt c a) :=
  Classical.dec _

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem legKeep_self (c₀ : Leg) (keepAt : A c₀ → Prop) :
    legKeep (A := A) c₀ keepAt c₀ = keepAt := by
  simp [legKeep]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Off the constrained leg the predicate is identically true. -/
theorem legKeep_eq_of_ne {c₀ c : Leg} (keepAt : A c₀ → Prop) (h : c₀ ≠ c) :
    legKeep (A := A) c₀ keepAt c = fun _ ↦ True := by
  simp [legKeep, h]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- **A block address survives a leg-local selection exactly when its own `c₀`-label does.**  This
one-line reduction is the whole reason `[DuanWuZhou2022]`'s repair needs a single union bound
rather than the three-leg recursion. -/
theorem legKeep_iff (c₀ : Leg) (keepAt : A c₀ → Prop) (s : BlockAddress A) :
    (∀ c, legKeep (A := A) c₀ keepAt c (s c)) ↔ keepAt (s c₀) := by
  constructor
  · intro h
    simpa using h c₀
  · intro h c
    by_cases hc : c₀ = c
    · subst hc
      simpa using h
    · rw [legKeep_eq_of_ne keepAt hc]
      trivial

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Composing a leg-local predicate with a legwise relabeling only changes the constrained leg's
predicate. -/
theorem legKeep_comp_symm (c₀ : Leg) (keepAt : A c₀ → Prop)
    (e : ∀ c, Equiv.Perm (A c)) (c : Leg) (b : A c) :
    legKeep (A := A) c₀ keepAt c ((e c).symm b) ↔
      legKeep (A := A) c₀ (fun a ↦ keepAt ((e c₀).symm a)) c b := by
  by_cases hc : c₀ = c
  · subst hc
    simp
  · rw [legKeep_eq_of_ne keepAt hc, legKeep_eq_of_ne _ hc]

/-! ## Broken copies -/

/-- **A broken copy of `P`.**  Every block whose leg-`c₀` label satisfies `hole` is zeroed out;
all other blocks, and all blocks on the other two legs, are untouched.

This is `[DuanWuZhou2022]`'s *broken copy of a standard form tensor* (Definition 5.2), stated for
an arbitrary partitioned tensor and an arbitrary leg. -/
noncomputable def PartitionedTensor.holeSelect
    (P : PartitionedTensor (K := K) (A := A) V) (c₀ : Leg) (hole : A c₀ → Prop) :
    PartitionedTensor (K := K) (A := A) V :=
  P.select (legKeep c₀ fun a ↦ ¬ hole a)

/-- Exact membership criterion for a broken copy: an address survives iff it was supported and its
leg-`c₀` label is not a hole. -/
@[simp] theorem PartitionedTensor.mem_holeSelect_support
    (P : PartitionedTensor (K := K) (A := A) V) (c₀ : Leg) (hole : A c₀ → Prop)
    (s : BlockAddress A) :
    s ∈ (P.holeSelect c₀ hole).support ↔ s ∈ P.support ∧ ¬ hole (s c₀) := by
  rw [PartitionedTensor.holeSelect, PartitionedTensor.mem_select_support, legKeep_iff]

/-- Breaking a copy does not change any constituent; only the support shrinks. -/
@[simp] theorem PartitionedTensor.holeSelect_constituent
    (P : PartitionedTensor (K := K) (A := A) V) (c₀ : Leg) (hole : A c₀ → Prop) :
    (P.holeSelect c₀ hole).constituent = P.constituent := rfl

/-- Two successive leg-local selections are one leg-local selection by the conjunction. -/
theorem PartitionedTensor.select_select_legKeep
    (P : PartitionedTensor (K := K) (A := A) V) (c₀ : Leg) (p q : A c₀ → Prop) :
    (P.select (legKeep c₀ p)).select (legKeep c₀ q) =
      P.select (legKeep c₀ fun a ↦ p a ∧ q a) := by
  classical
  apply PartitionedTensor.ext
  · ext s
    rw [PartitionedTensor.mem_select_support, PartitionedTensor.mem_select_support,
      PartitionedTensor.mem_select_support, legKeep_iff, legKeep_iff, legKeep_iff, and_assoc]
  · rfl

/-! ## The identification step -/

/-- **The leg-local blocks of `P` are covered exactly once by the refined selections.**

If `choose` names, for each leg-`c₀` label of a supported address, the unique index whose
predicate that label satisfies, then the selected pieces sum to the whole tensor.  This is the
"identify all copies" step of `[DuanWuZhou2022]`'s proof, in which each surviving small Z-block
contributes to exactly one copy.

Proof sketch: unfold `realize` to the sum over the support; the hypothesis rewrites the selection
filter of index `t` to the fiber `choose (s c₀) = t`, and `Finset.sum_fiberwise` reassembles the
fibers into the full support sum. -/
theorem PartitionedTensor.sum_realize_legSelect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PartitionedTensor (K := K) (A := A) V) (c₀ : Leg)
    (p : ι → A c₀ → Prop) (choose : A c₀ → ι)
    (hchoose : ∀ s ∈ P.support, ∀ t, p t (s c₀) ↔ choose (s c₀) = t) :
    ∑ t, (P.select (legKeep c₀ (p t))).realize = P.realize := by
  classical
  have hfilter : ∀ t : ι,
      (P.support.filter fun s ↦ ∀ c, legKeep (A := A) c₀ (p t) c (s c)) =
        P.support.filter fun s ↦ choose (s c₀) = t := by
    intro t
    apply Finset.filter_congr
    intro s hs
    rw [legKeep_iff]
    exact hchoose s hs t
  have hgoal :
      (∑ t : ι, ∑ s ∈ P.support.filter fun s ↦ choose (s c₀) = t,
          map (blockInclude (K := K) (V := V) s) (P.constituent s)) =
        ∑ s ∈ P.support, map (blockInclude (K := K) (V := V) s) (P.constituent s) :=
    Finset.sum_fiberwise P.support (fun s ↦ choose (s c₀)) _
  calc
    (∑ t : ι, (P.select (legKeep c₀ (p t))).realize)
        = ∑ t : ι, ∑ s ∈ P.support.filter fun s ↦ choose (s c₀) = t,
            map (blockInclude (K := K) (V := V) s) (P.constituent s) := by
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          show realizePartition ((P.select (legKeep c₀ (p t))).support)
              (P.select (legKeep c₀ (p t))).constituent = _
          rw [PartitionedTensor.select]
          rw [realizePartition]
          exact Finset.sum_congr (by rw [← hfilter t]) fun s _ ↦ rfl
    _ = P.realize := hgoal

/-! ## The Hole Lemma -/

/-- **The single-leg Hole Lemma** (`[DuanWuZhou2022]`, Lemma 5.3).

Let `P` be a partitioned tensor and let `hole t` be the set of leg-`c₀` labels destroyed in the
`t`-th broken copy.  Suppose a function `choose` names, for every supported address, a copy in
which that address's leg-`c₀` label is *not* a hole.  Then the direct sum of the broken copies
restricts onto the intact `P`:

`⊕_t P[holes t] ⊵ P`.

Proof sketch, following the paper: in copy `t`, additionally zero out every block whose `c₀`-label
`a` has `choose a ≠ t` (this is again a leg-local selection, so it is an exact restriction).  The
refined copies now have pairwise disjoint supports whose union is `P.support` — precisely because
`choose a` is a *single* index and the covering hypothesis makes that index legal.  Identifying
the copies (`Restricts.indexedDirectSum_to_sum`) therefore produces `∑_t P[…] = P`
(`PartitionedTensor.sum_realize_legSelect`).

Nothing is assumed about how the copies arose: the conclusion is a proved restriction chain. -/
theorem Restricts.indexedDirectSum_legHoleRepair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PartitionedTensor (K := K) (A := A) V) (c₀ : Leg)
    (hole : ι → A c₀ → Prop) (choose : A c₀ → ι)
    (hcover : ∀ s ∈ P.support, ¬ hole (choose (s c₀)) (s c₀)) :
    Restricts
      (Tensor.indexedDirectSum (V := fun _ : ι ↦ PartitionedSpace K V)
        fun t ↦ (P.holeSelect c₀ (hole t)).realize)
      P.realize := by
  classical
  have hstep : ∀ t : ι,
      Restricts (P.holeSelect c₀ (hole t)).realize
        (P.select (legKeep c₀ fun a ↦ ¬ hole t a ∧ choose a = t)).realize := by
    intro t
    have h := Restricts.partitionedSelect (P.holeSelect c₀ (hole t))
      (legKeep c₀ fun a ↦ choose a = t)
    rwa [PartitionedTensor.holeSelect, PartitionedTensor.select_select_legKeep] at h
  refine (Restricts.indexedDirectSum_to_sum hstep).trans (Restricts.of_eq ?_)
  refine PartitionedTensor.sum_realize_legSelect P c₀ _ choose ?_
  intro s hs t
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro rfl
    exact ⟨hcover s hs, rfl⟩

/-! ## Shuffling a broken copy -/

namespace PartitionedTensor.StructureRelabeling

variable {P : PartitionedTensor (K := K) (A := A) V}

/-- **A structure-preserving relabeling carries a broken copy to the copy with moved holes.**

This is the tensor-level content of the shuffling step in `[DuanWuZhou2022]` §5: renaming the
variables of a broken copy by `φ` yields a broken copy of the *same* tensor whose hole set is the
`φ`-image of the original hole set.  The two ingredients are (i) `φ` preserves the intact tensor
(`StructureRelabeling.invariant`) and (ii) hole membership is a leg-local condition, so it is
transported by the leg-`c₀` component of `φ` alone. -/
theorem holeSelect_reindex_eq (r : P.StructureRelabeling) (c₀ : Leg) (hole : A c₀ → Prop) :
    (P.holeSelect c₀ hole).reindex r.partEquiv r.blockEquiv =
      P.holeSelect c₀ fun a ↦ hole ((r.partEquiv c₀).symm a) := by
  classical
  rw [PartitionedTensor.holeSelect, PartitionedTensor.reindex_select, r.invariant]
  apply PartitionedTensor.ext
  · ext s
    rw [PartitionedTensor.mem_select_support, PartitionedTensor.mem_holeSelect_support]
    constructor
    · rintro ⟨hs, hkeep⟩
      refine ⟨hs, ?_⟩
      have h := (legKeep_comp_symm c₀ (fun a ↦ ¬ hole a) r.partEquiv c₀ (s c₀)).mp (hkeep c₀)
      simpa using h
    · rintro ⟨hs, hnot⟩
      refine ⟨hs, fun c ↦ ?_⟩
      refine (legKeep_comp_symm c₀ (fun a ↦ ¬ hole a) r.partEquiv c (s c)).mpr ?_
      exact (legKeep_iff c₀ (fun a ↦ ¬ hole ((r.partEquiv c₀).symm a)) s).mpr hnot c
  · rfl

/-- **A structure-preserving relabeling permutes the supported block addresses.**

This is `[DuanWuZhou2022]`'s Claim 1 (`hole_lemma.tex` l.95) in its general form: the relabeling
sends *available* blocks to available blocks, so it restricts to a permutation of them.  In the
paper the claim is proved by hand for the shuffling group; here it is a consequence of the single
invariance equation `P.reindex partEquiv blockEquiv = P`. -/
theorem mem_support_blockAddressCongr (r : P.StructureRelabeling)
    {s : BlockAddress A} (hs : s ∈ P.support) :
    blockAddressCongr r.partEquiv s ∈ P.support := by
  classical
  have hsupport : (P.reindex r.partEquiv r.blockEquiv).support = P.support :=
    congrArg PartitionedTensor.support r.invariant
  rw [PartitionedTensor.reindex_support] at hsupport
  rw [← hsupport]
  exact Finset.mem_map_of_mem _ hs

/-- Semantic form: a shuffled broken copy is isomorphic to the broken copy with moved holes. -/
theorem holeSelect_isomorphic (r : P.StructureRelabeling) (c₀ : Leg) (hole : A c₀ → Prop) :
    Isomorphic (P.holeSelect c₀ hole).realize
      (P.holeSelect c₀ fun a ↦ hole ((r.partEquiv c₀).symm a)).realize := by
  have h := Isomorphic.partitionedReindex (P.holeSelect c₀ hole) r.partEquiv r.blockEquiv
  rwa [holeSelect_reindex_eq] at h

end PartitionedTensor.StructureRelabeling

/-- **The Hole Lemma with shuffling** (`[DuanWuZhou2022]`, Lemma 5.3 as actually applied).

Each broken copy is first renamed by its own structure-preserving relabeling `r t`.  The covering
hypothesis is therefore stated for the *moved* hole sets: a supported address must have a copy `t`
whose relabeling pulls the address's leg-`c₀` label out of `hole t`.  The conclusion is again a
proved restriction from the direct sum of the original broken copies. -/
theorem Restricts.indexedDirectSum_shuffledLegHoleRepair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PartitionedTensor (K := K) (A := A) V) (c₀ : Leg)
    (r : ι → P.StructureRelabeling) (hole : ι → A c₀ → Prop) (choose : A c₀ → ι)
    (hcover : ∀ s ∈ P.support,
      ¬ hole (choose (s c₀)) (((r (choose (s c₀))).partEquiv c₀).symm (s c₀))) :
    Restricts
      (Tensor.indexedDirectSum (V := fun _ : ι ↦ PartitionedSpace K V)
        fun t ↦ (P.holeSelect c₀ (hole t)).realize)
      P.realize := by
  classical
  have hmove : ∀ t : ι,
      Restricts (P.holeSelect c₀ (hole t)).realize
        (P.holeSelect c₀ fun a ↦ hole t (((r t).partEquiv c₀).symm a)).realize :=
    fun t ↦ (PartitionedTensor.StructureRelabeling.holeSelect_isomorphic
      (r t) c₀ (hole t)).restricts
  exact (Restricts.indexedDirectSum hmove).trans
    (Restricts.indexedDirectSum_legHoleRepair P c₀
      (fun t a ↦ hole t (((r t).partEquiv c₀).symm a)) choose hcover)

/-! ## Position shuffles of a positive power

`[DuanWuZhou2022]`'s shuffling group acts by permuting word positions, and the repair argument
needs the *inverse* of such a shuffle — `holeSelect_reindex_eq` transports a hole set along
`(partEquiv c₀).symm`.  The following identification keeps that inverse inside the same family of
position permutations instead of leaving an opaque `Equiv.symm`.
-/

/-- **The inverse of a position shuffle is the position shuffle by the inverse permutation.**

Proof sketch: position relabeling is a monoid homomorphism into the permutations of words
(`positiveWordPositionEquiv_mul`, `positiveWordPositionEquiv_one`), so applying it to
`σ⁻¹ * σ = 1` exhibits the shuffle by `σ⁻¹` as a right inverse. -/
theorem positiveWordPositionEquiv_symm (I : Type w) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (positiveWordPositionEquiv I n σ).symm = positiveWordPositionEquiv I n σ.symm := by
  apply Equiv.ext
  intro word
  refine (Equiv.symm_apply_eq _).mpr ?_
  have hone : (σ.symm * σ : Equiv.Perm (Fin (n + 1))) = 1 := by
    apply Equiv.ext
    intro i
    simp
  have hmul := positiveWordPositionEquiv_mul I n σ.symm σ
  rw [hone, positiveWordPositionEquiv_one] at hmul
  have := congrArg (fun e ↦ e word) hmul
  simpa using this

/-! ## A tiny inhabited instance

`DESIGN.md` requires a deliberately tiny client for every major semantic operation.  Two failure
modes are guarded here.  First, *vacuity*: if the broken copies were secretly intact, the Hole
Lemma would be a triviality, so the instance exhibits an address that is genuinely destroyed in
each copy.  Second, *direction*: the conclusion must be `⊕ broken ⊵ intact`, never the reverse,
and a single broken copy must not suffice.
-/

section TinyInstance

variable (K : Type u) [CommSemiring K]

/-- Two block labels on every tensor leg. -/
abbrev TinyHoleLabel : Leg → Type := fun _ ↦ Fin 2

/-- Every block of the tiny partition carries the ground ring on all three legs. -/
abbrev TinyHoleBlockSpace : ∀ c, TinyHoleLabel c → Type u := fun _ _ ↦ K

/-- The block address using the label `i` on every leg. -/
def tinyHoleAddress (i : Fin 2) : BlockAddress TinyHoleLabel := fun _ ↦ i

/-- A two-block partitioned tensor whose two supported addresses are the diagonal ones. -/
noncomputable def tinyHolePartition :
    PartitionedTensor (K := K) (A := TinyHoleLabel) (TinyHoleBlockSpace K) where
  support := {tinyHoleAddress 0, tinyHoleAddress 1}
  constituent := fun _ ↦ Tensor.pure (K := K) fun _ ↦ (1 : K)

@[simp] theorem tinyHolePartition_support :
    (tinyHolePartition K).support = {tinyHoleAddress 0, tinyHoleAddress 1} := rfl

/-- The `t`-th broken copy destroys exactly the Z-block labelled `t`. -/
def tinyHole (t : Fin 2) : Fin 2 → Prop := fun a ↦ a = t

/-- **The broken copies really are broken.**  The diagonal address labelled `t` is missing from
the `t`-th copy. -/
theorem tinyHoleAddress_notMem_holeSelect (t : Fin 2) :
    tinyHoleAddress t ∉
      ((tinyHolePartition K).holeSelect Leg.Z (tinyHole t)).support := by
  rw [PartitionedTensor.mem_holeSelect_support]
  rintro ⟨-, hnot⟩
  exact hnot rfl

/-- **The other diagonal address survives.**  Together with the previous theorem this shows each
copy is a proper, nonempty piece of the tiny partition. -/
theorem tinyHoleAddress_mem_holeSelect (t : Fin 2) :
    tinyHoleAddress (t + 1) ∈
      ((tinyHolePartition K).holeSelect Leg.Z (tinyHole t)).support := by
  rw [PartitionedTensor.mem_holeSelect_support]
  refine ⟨?_, ?_⟩
  · fin_cases t <;> simp [tinyHolePartition]
  · show ¬ (tinyHoleAddress (t + 1) Leg.Z = t)
    show ¬ (t + 1 = t)
    fin_cases t <;> decide

/-- **The Hole Lemma, exercised on the tiny instance.**  Neither broken copy contains the whole
tensor, yet their direct sum restricts onto it: the label `a` survives in the copy `a + 1`. -/
theorem tiny_indexedDirectSum_legHoleRepair :
    Restricts
      (Tensor.indexedDirectSum
        (V := fun _ : Fin 2 ↦ PartitionedSpace K (TinyHoleBlockSpace K))
        fun t ↦ ((tinyHolePartition K).holeSelect Leg.Z (tinyHole t)).realize)
      (tinyHolePartition K).realize :=
  Restricts.indexedDirectSum_legHoleRepair (tinyHolePartition K) Leg.Z tinyHole
    (fun a ↦ a + 1) (by
      intro s _hs
      show ¬ (s Leg.Z = s Leg.Z + 1)
      have h : ∀ a : Fin 2, ¬ (a = a + 1) := by decide
      exact h (s Leg.Z))

end TinyInstance

end AlgebraicComplexity.Tensor
