/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTargetTypical
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSharpDegree

/-!
# The six digits of a six-orientation block label

Layer 4 (`AlgebraicComplexity/Examples/`).  A block label of `dwz63SymSixPartition K` carries, on
each of the three target legs, one coarse Coppersmith--Winograd square degree per leg permutation:
`DwzSymSixBlock c = ((Fin 5 × Fin 5) × Fin 5) × ((Fin 5 × Fin 5) × Fin 5)`, in the association of
`PartitionedTensor.symSixPartition`.  There are therefore two ways to read one orientation out of
one label, and the difference between them is the whole content of this module.

## Target and source reading

* `dwz63TargetLetter o w` reads the `o`-th digit at **each leg where it sits**, with no transport:
  `(dwz63TargetLetter o w) c = dwz63SymSixDigit o (w c)`.  This is the reading in which the six
  orientations of the power are six *independent* coordinates of a single label, so it is the
  reading a count factorizes along.
* `dwz63SourceLetter o w` (committed in `Examples/DuanWuZhouLevelTwoOrientationTypical.lean`)
  transports back into the source partition's own address space, reading the `o`-th digit at leg
  `σ_o c`.

Both readings are committed elsewhere --- `dwz63TargetLetter` in
`Examples/DuanWuZhouLevelTwoTargetTypical.lean`, together with
`dwz63TargetLetter_eq_cwSquarePermute` relating them.  What this module adds is the *digit*
presentation `dwz63TargetLetter_apply` and everything it makes possible.  Since the fifteen coarse
addresses are cut out by the *symmetric* condition "the three degrees sum to four", the two
readings agree on every support question --- `dwz63SourceLetter_mem_cwSquareSupport_iff`.

## Principal results

* `dwz63TargetTupleEquiv : BlockAddress DwzSymSixBlock ≃ (Fin 6 → CWSquareAddress)` --- the target
  reading is a **bijection**, transport-free in both directions.  This is the structure a
  six-orientation count factorizes through: `5 ^ 18` labels on either side, nothing collapsed.
* `mem_dwz63SymSixPartition_support_iff` (and `..._iff_target`) --- membership in the
  six-orientation support **is** the conjunction of the six per-orientation support conditions.
  The forward half is the committed `dwz63SourceLetter_mem_cwSquareSupport`; the *converse* is
  what a counting client needs, and it is the half that lets six arbitrary supported coarse
  addresses be assembled into a genuine block label.
* `dwz63TargetLetter_mem_cwSquareSupport` --- the anti-vacuity pin
  `Examples/DuanWuZhouLevelTwoTargetTypical.lean` records as owed, discharged.
* `dwz63TargetTupleEquiv_symm_mem_support` --- six arbitrary supported coarse addresses assemble
  into a supported label.  The word-level assembly built on it, and the product count it makes
  possible, live in `Examples/DuanWuZhouLevelTwoTargetWordCount.lean`.

## Note on the proof of the support characterization

The iff is proved from scratch rather than by extending the committed one-directional
`dwz63SourceLetter_mem_cwSquareSupport`.  That is deliberate: *applying* that constant from a
downstream module forces a defeq check that does not terminate inside a million heartbeats, while
re-running its rewrite chain here costs a few seconds.  The two statements are of course the same
mathematics, and the committed one remains the forward half's reference.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The six digits of one leg label -/

/-- **The `o`-th base-five digit of a six-orientation block label at one leg**, in the association
`((σ₁, σ₂), σ₃), ((σ₄, σ₅), σ₆)` of `PartitionedTensor.symSixPartition`. -/
def dwz63SymSixDigit : Fin 6 → DwzSymSixBlock .X → Fin 5 :=
  ![fun d ↦ d.1.1.1, fun d ↦ d.1.1.2, fun d ↦ d.1.2,
    fun d ↦ d.2.1.1, fun d ↦ d.2.1.2, fun d ↦ d.2.2]

/-- **Assemble one leg label from its six digits.** -/
def dwz63SymSixOfDigits (g : Fin 6 → Fin 5) : DwzSymSixBlock .X :=
  (((g 0, g 1), g 2), ((g 3, g 4), g 5))

@[simp] theorem dwz63SymSixDigit_ofDigits (g : Fin 6 → Fin 5) (o : Fin 6) :
    dwz63SymSixDigit o (dwz63SymSixOfDigits g) = g o := by
  fin_cases o <;> rfl

-- ELABORATION RISK: `have h0 : d0 = e0 := h 0` relies on `![…] 0` reducing to its head by whnf.
-- Fallback if it does not: `simpa [dwz63SymSixDigit] using h 0`.
/-- **A leg label is determined by its six digits.** -/
theorem dwz63SymSixBlock_ext {d e : DwzSymSixBlock .X}
    (h : ∀ o : Fin 6, dwz63SymSixDigit o d = dwz63SymSixDigit o e) : d = e := by
  obtain ⟨⟨⟨d0, d1⟩, d2⟩, ⟨⟨d3, d4⟩, d5⟩⟩ := d
  obtain ⟨⟨⟨e0, e1⟩, e2⟩, ⟨⟨e3, e4⟩, e5⟩⟩ := e
  have h0 : d0 = e0 := h 0
  have h1 : d1 = e1 := h 1
  have h2 : d2 = e2 := h 2
  have h3 : d3 = e3 := h 3
  have h4 : d4 = e4 := h 4
  have h5 : d5 = e5 := h 5
  subst h0; subst h1; subst h2; subst h3; subst h4; subst h5
  rfl

/-- **The six digits of one leg label are a coordinate system for it.** -/
def dwz63SymSixDigitEquiv : DwzSymSixBlock .X ≃ (Fin 6 → Fin 5) where
  toFun d := fun o ↦ dwz63SymSixDigit o d
  invFun := dwz63SymSixOfDigits
  left_inv _d := dwz63SymSixBlock_ext fun o ↦ dwz63SymSixDigit_ofDigits _ o
  right_inv g := funext fun o ↦ dwz63SymSixDigit_ofDigits g o

/-! ## The target reading, in digit coordinates -/

/-- **The committed target reading is the digit reading.**  `dwz63TargetLetter` of
`Examples/DuanWuZhouLevelTwoTargetTypical.lean` takes the `o`-th component at each leg where it
sits; that is exactly the `o`-th base-five digit of that leg's label. -/
theorem dwz63TargetLetter_apply (o : Fin 6) (w : BlockAddress DwzSymSixBlock) (c : Leg) :
    dwz63TargetLetter o w c = dwz63SymSixDigit o (w c) := by
  fin_cases o <;> rfl

/-- **The two readings differ by the orientation's own leg permutation, pointwise.**  The
`funext`-free companion of `dwz63TargetLetter_eq_cwSquarePermute`. -/
theorem dwz63SourceLetter_eq_dwz63TargetLetter (o : Fin 6) (w : BlockAddress DwzSymSixBlock)
    (c : Leg) :
    dwz63SourceLetter o w c = dwz63TargetLetter o w (dwz63Orientation o c) := by
  fin_cases o <;> rfl

/-- **The target reading of a six-orientation block label is a bijection onto six independent
coarse addresses.**  Both directions are transport-free: the inverse assembles the six digits at
each leg separately.  Nothing is collapsed --- `5 ^ 18` labels on either side. -/
def dwz63TargetTupleEquiv : BlockAddress DwzSymSixBlock ≃ (Fin 6 → CWSquareAddress) where
  toFun w := fun o ↦ dwz63TargetLetter o w
  invFun f := fun c ↦ dwz63SymSixOfDigits fun o ↦ f o c
  left_inv w := by
    funext c
    refine dwz63SymSixBlock_ext fun o ↦ ?_
    simp only [dwz63SymSixDigit_ofDigits, dwz63TargetLetter_apply]
  right_inv f := by
    funext o c
    simp only [dwz63TargetLetter_apply, dwz63SymSixDigit_ofDigits]

@[simp] theorem dwz63TargetLetter_dwz63TargetTupleEquiv_symm (f : Fin 6 → CWSquareAddress)
    (o : Fin 6) :
    dwz63TargetLetter o (dwz63TargetTupleEquiv.symm f) = f o :=
  congrFun (dwz63TargetTupleEquiv.apply_symm_apply f) o

/-! ## The two readings agree on every support question -/

/-- Undoing a leg permutation of a coarse address. -/
theorem cwSquarePermute_symm_cwSquarePermute (e : Orientation) (addr : CWSquareAddress) :
    cwSquarePermute e.symm (cwSquarePermute e addr) = addr := by
  funext c
  rw [cwSquarePermute_apply, Equiv.symm_symm, cwSquarePermute_apply, Equiv.symm_apply_apply]

/-- **The source reading of an orientation is supported exactly when its target reading is.**  The
degree-four antidiagonal is symmetric, so `mem_cwSquareSupport_cwSquarePermute` runs in both
directions. -/
theorem dwz63SourceLetter_mem_cwSquareSupport_iff (o : Fin 6) (w : BlockAddress DwzSymSixBlock) :
    dwz63SourceLetter o w ∈ cwSquareSupport ↔ dwz63TargetLetter o w ∈ cwSquareSupport := by
  rw [dwz63TargetLetter_eq_cwSquarePermute]
  refine ⟨fun h ↦ mem_cwSquareSupport_cwSquarePermute _ h, fun h ↦ ?_⟩
  have h2 := mem_cwSquareSupport_cwSquarePermute (dwz63Orientation o).symm h
  rwa [cwSquarePermute_symm_cwSquarePermute] at h2

/-! ## Support membership is exactly the six per-orientation conditions -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **Membership in the six-orientation support is the conjunction of the six per-orientation
support conditions.**

The forward half is the committed `dwz63SourceLetter_mem_cwSquareSupport`, re-derived here rather
than applied (see the module docstring).  The converse is the half a counting client needs: six
arbitrary supported coarse addresses assemble into a genuine block label of
`dwz63SymSixPartition K`, so the six orientations really are free coordinates and the typical
family is a product. -/
theorem mem_dwz63SymSixPartition_support_iff (K : Type u) [CommRing K]
    (w : BlockAddress DwzSymSixBlock) :
    w ∈ (dwz63SymSixPartition K).support ↔
      ∀ o : Fin 6, dwz63SourceLetter o w ∈ cwSquareSupport := by
  classical
  have hperm : ∀ (e : Orientation)
      (t : BlockAddress (PermutedBlockIndex e fun _ : Leg ↦ Fin 5)) (c : Leg),
      (permuteBlockAddress e).symm t c = t (e c) := by
    intro e t c
    have h := permuteBlockAddress_symm_apply_apply (A := fun _ : Leg ↦ Fin 5) e t (e c)
    rwa [Equiv.symm_apply_apply] at h
  have e1 : ((permuteBlockAddress cycle).symm fun c ↦ (w c).1.1.2)
      = fun c ↦ (w (cycle c)).1.1.2 := funext fun c ↦ hperm cycle _ c
  have e2 : ((permuteBlockAddress cycle.symm).symm fun c ↦ (w c).1.2)
      = fun c ↦ (w (cycle.symm c)).1.2 := funext fun c ↦ hperm cycle.symm _ c
  have e3 : ((permuteBlockAddress swapXY).symm fun c ↦ (w c).2.1.1)
      = fun c ↦ (w (swapXY c)).2.1.1 := funext fun c ↦ hperm swapXY _ c
  have e4 : ((permuteBlockAddress (cycle.trans swapXY)).symm fun c ↦ (w c).2.1.2)
      = fun c ↦ (w ((cycle.trans swapXY) c)).2.1.2 :=
    funext fun c ↦ hperm (cycle.trans swapXY) _ c
  have e5 : ((permuteBlockAddress (cycle.symm.trans swapXY)).symm fun c ↦ (w c).2.2)
      = fun c ↦ (w ((cycle.symm.trans swapXY) c)).2.2 :=
    funext fun c ↦ hperm (cycle.symm.trans swapXY) _ c
  rw [dwz63SymSixPartition, PartitionedTensor.symSixPartition,
    PartitionedTensor.symThreePartition, PartitionedTensor.swapSymThreePartition]
  simp only [PartitionedTensor.mem_external_support, PartitionedTensor.mem_permute_support,
    cwSquarePartitionedTensor_support, e1, e2, e3, e4, e5]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, ⟨h3, h4⟩, h5⟩ o
    fin_cases o
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro h
    exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, ⟨h 3, h 4⟩, h 5⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **Support membership in the target reading.**  This is the form a product count uses: the six
target letters range independently over the fifteen coarse addresses. -/
theorem mem_dwz63SymSixPartition_support_iff_target (K : Type u) [CommRing K]
    (w : BlockAddress DwzSymSixBlock) :
    w ∈ (dwz63SymSixPartition K).support ↔
      ∀ o : Fin 6, dwz63TargetLetter o w ∈ cwSquareSupport := by
  rw [mem_dwz63SymSixPartition_support_iff]
  exact forall_congr' fun o ↦ dwz63SourceLetter_mem_cwSquareSupport_iff o w

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **The anti-vacuity pin owed by `Examples/DuanWuZhouLevelTwoTargetTypical.lean`.**  The
untransported component of a supported six-orientation label is a genuine coarse address.  Routing
it through `mem_dwz63SymSixPartition_support_iff` --- which re-derives the support unfolding here
rather than applying the committed `dwz63SourceLetter_mem_cwSquareSupport` --- avoids the `whnf`
loop that blocked it there. -/
theorem dwz63TargetLetter_mem_cwSquareSupport (K : Type u) [CommRing K]
    (w : BlockAddress DwzSymSixBlock) (hw : w ∈ (dwz63SymSixPartition K).support) (o : Fin 6) :
    dwz63TargetLetter o w ∈ cwSquareSupport := by
  revert hw
  rw [mem_dwz63SymSixPartition_support_iff_target]
  exact fun h ↦ h o

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **Six supported coarse addresses assemble into a supported block label.** -/
theorem dwz63TargetTupleEquiv_symm_mem_support (K : Type u) [CommRing K]
    {f : Fin 6 → CWSquareAddress} (hf : ∀ o : Fin 6, f o ∈ cwSquareSupport) :
    dwz63TargetTupleEquiv.symm f ∈ (dwz63SymSixPartition K).support := by
  rw [mem_dwz63SymSixPartition_support_iff_target]
  intro o
  rw [dwz63TargetLetter_dwz63TargetTupleEquiv_symm]
  exact hf o

end AlgebraicComplexity.Examples
