/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrientationTypical

/-!
# Target-coordinate typicality of a six-orientation block word

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoOrientationTypical.lean`
reads the `o`-th component of a `dwz63SymSixPartition` label *in the source partition's own
address space*, by transporting it back along `(permuteBlockAddress e_o).symm`.  That is the right
convention for a value lane that wants each copy's coarse letters to be literal
`cwSquarePartitionedTensor` constituents, and it is kept, frozen, as posted.

It is **not** the convention the copy count can use.  The joint hash of
`Examples/DuanWuZhouLevelTwoJointHashing.lean` acts on the *target* legs of the six-orientation
power: `dwz63_x_injOn_jointRetained` makes the retained addresses distinct in
`a .X : PositiveWord (DwzSymSixBlock .X) n`, whose `o`-th component is the label as it sits in
`PermutedBlockIndex e_o`.  Under source-coordinate typicality that component's marginal is the
source `alpha` marginal at leg `e_o⁻¹ .X`, so as `e_o` ranges over `Equiv.Perm Leg` the target
`X`-leg sees each source leg twice --- four `dwz63AlphaX` and two `dwz63AlphaZ`.  The retained
count is then at most `exp((4 H_e(alpha_X) + 2 H_e(alpha_Z)) n)`, while
`dwz63TrueCopyRate ^ (6 n)` asks for `exp(6 H_e(alpha_X) n)`; the deficit is `0.019` nats per
position against a margin of `10 ^ (-6)`.

This module supplies the other convention.  `dwz63TargetLetter` reads the `o`-th component **as it
sits**, with no transport, so every copy's target `X`-leg carries `dwz63AlphaX` and its target
`Z`-leg carries `dwz63AlphaZ` --- exactly the two marginals the repo's rate arithmetic is built
from.  The price, made explicit by `dwz63TargetTypical_iff_orientationTypical_comp`, is that the
*source* sub-word of copy `o` then has type `dwz63AlphaAddress ∘ cwSquarePermute e_o` rather than
`dwz63AlphaAddress`; since the six-fold symmetrized value is invariant under permuting a
component's legs, that costs the value lane nothing, and the lemma lets either lane consume
whichever form it wants.

## Anti-vacuity

`dwz63TargetLetter_mem_cwSquareSupport`: the untransported component is still a genuine coarse
address.  It has to be checked, and it holds for the specific reason that
`mem_cwSquareAntidiagonal_iff` records --- the degree-four antidiagonal is *symmetric*, so it is
stable under every leg permutation.  Nothing about the fifteen cells' `alpha` weights is
symmetric, which is exactly why the two typicality conventions differ.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

set_option maxRecDepth 100000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSimpArgs false

/-! ## Leg permutations of a coarse address -/

/-- Reading a coarse square address through a leg permutation, as a self-equivalence of
`CWSquareAddress`.  This is `Tensor.permuteBlockAddress` at the constant block family, packaged so
that it can be composed and inverted without dependent-type friction. -/
def cwSquarePermute (e : Orientation) : CWSquareAddress ≃ CWSquareAddress :=
  Equiv.piCongrLeft' (fun _ : Leg ↦ Fin 5) e

@[simp] theorem cwSquarePermute_apply (e : Orientation) (addr : CWSquareAddress) (c : Leg) :
    cwSquarePermute e addr c = addr (e.symm c) := rfl

/-- It is `Tensor.permuteBlockAddress`, definitionally. -/
theorem cwSquarePermute_eq_permuteBlockAddress (e : Orientation) (addr : CWSquareAddress) :
    cwSquarePermute e addr = permuteBlockAddress (A := fun _ : Leg ↦ Fin 5) e addr := rfl

/-- **The coarse support is the degree-four antidiagonal, as a predicate.** -/
theorem mem_cwSquareAntidiagonal_iff (addr : CWSquareAddress) :
    addr ∈ cwSquareAntidiagonal ↔
      (addr .X).val + (addr .Y).val + (addr .Z).val = 4 := by
  revert addr
  decide

/-- **The coarse support is symmetric.**  The degree-four condition is a sum, so every leg
permutation preserves it.  This is what makes the untransported component of a six-orientation
label a legitimate coarse address. -/
theorem mem_cwSquareSupport_cwSquarePermute (e : Orientation) {addr : CWSquareAddress}
    (h : addr ∈ cwSquareSupport) : cwSquarePermute e addr ∈ cwSquareSupport := by
  rw [cwSquareSupport_eq_antidiagonal] at h ⊢
  rw [mem_cwSquareAntidiagonal_iff] at h ⊢
  calc (cwSquarePermute e addr .X).val + (cwSquarePermute e addr .Y).val
        + (cwSquarePermute e addr .Z).val
      = (addr .X).val + (addr .Y).val + (addr .Z).val :=
        leg_add_three_comp_equiv e.symm fun c ↦ (addr c).val
    _ = 4 := h

/-! ## The six orientations, named -/

/-- The six leg permutations of `PartitionedTensor.symSixPartition`, in the order its nested
external product associates them. -/
def dwz63Orientation : Fin 6 → Orientation :=
  ![1, cycle, cycle.symm, swapXY, cycle.trans swapXY, cycle.symm.trans swapXY]

/-! ## The target letter -/

/-- **The `o`-th oriented coarse letter of a six-orientation block label, read as it sits.**

No transport: the component is taken at the *target* leg, which is the leg the joint hash and the
`X`-injectivity of `dwz63_x_injOn_jointRetained` actually see. -/
def dwz63TargetLetter : Fin 6 → BlockAddress DwzSymSixBlock → CWSquareAddress :=
  ![fun w c ↦ (w c).1.1.1,
    fun w c ↦ (w c).1.1.2,
    fun w c ↦ (w c).1.2,
    fun w c ↦ (w c).2.1.1,
    fun w c ↦ (w c).2.1.2,
    fun w c ↦ (w c).2.2]

/-- **The two conventions differ by exactly one leg permutation.** -/
theorem dwz63TargetLetter_eq_cwSquarePermute (o : Fin 6) (w : BlockAddress DwzSymSixBlock) :
    dwz63TargetLetter o w = cwSquarePermute (dwz63Orientation o) (dwz63SourceLetter o w) := by
  funext c
  have h : ∀ (e : Orientation) (g : Leg → Fin 5), g c = g (e (e.symm c)) := by
    intro e g
    rw [Equiv.apply_symm_apply]
  rw [cwSquarePermute_apply]
  fin_cases o
  · rfl
  · exact h cycle fun d ↦ (w d).1.1.2
  · exact h cycle.symm fun d ↦ (w d).1.2
  · exact h swapXY fun d ↦ (w d).2.1.1
  · exact h (cycle.trans swapXY) fun d ↦ (w d).2.1.2
  · exact h (cycle.symm.trans swapXY) fun d ↦ (w d).2.2

/- **Anti-vacuity pin, DISCHARGED elsewhere.**  `dwz63TargetLetter o w ∈ cwSquareSupport` for
`w ∈ (dwz63SymSixPartition K).support` is proved as `dwz63TargetLetter_mem_cwSquareSupport` in
`AlgebraicComplexity/Examples/DuanWuZhouLevelTwoSixOrientationDigits.lean` (typical-count lane).
It cannot be stated, or audited, here: that module imports *this* one, so the dependency runs
downstream only --- consumers import `SixOrientationDigits`, never the reverse.  The content is
`mem_cwSquareSupport_cwSquarePermute` above: the degree-four antidiagonal is symmetric, hence
stable under every leg permutation.  Nothing below depends on the pin. -/

/-! ## The target sub-word and its typicality -/

/-- **The `o`-th target coarse sub-word of a six-orientation block word.** -/
noncomputable def dwz63TargetWord (K : Type u) [CommRing K] (n : ℕ) (o : Fin 6)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) : Fin (n + 1) → CWSquareAddress :=
  fun j ↦ dwz63TargetLetter o (positiveWordEquiv _ n q j).val

/-- The target sub-word is the source sub-word read through the orientation. -/
theorem dwz63TargetWord_eq (K : Type u) [CommRing K] (n : ℕ) (o : Fin 6)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) :
    dwz63TargetWord K n o q =
      fun j ↦ cwSquarePermute (dwz63Orientation o) (dwz63OrientedWord K n o q j) := by
  funext j
  exact dwz63TargetLetter_eq_cwSquarePermute o _

/-- **Target-coordinate typicality.**  Every one of the six components, read at its own target
leg, has letter type `WordType.proportionalCounts dwz63AlphaAddress t`.  Consequently every copy's
target `X`-leg carries `dwz63AlphaX` and its target `Z`-leg carries `dwz63AlphaZ`, which is the
normalization `dwz63TrueCopyRate ^ (6 * (n + 1))` is stated in. -/
def Dwz63TargetTypical (K : Type u) [CommRing K] (n t : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) : Prop :=
  ∀ o : Fin 6,
    WordType.multiplicity (dwz63TargetWord K n o q) =
      WordType.proportionalCounts dwz63AlphaAddress t

/-- Multiplicities transport along a bijection of the alphabet. -/
theorem multiplicity_comp_equiv {ι : Type*} [Fintype ι] {m : ℕ} (e : ι ≃ ι)
    (w : Fin m → ι) (a : ι) :
    WordType.multiplicity (fun j ↦ e (w j)) a = WordType.multiplicity w (e.symm a) := by
  classical
  unfold WordType.multiplicity
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h ↦ (Equiv.eq_symm_apply e).mpr h, fun h ↦ (Equiv.eq_symm_apply e).mp h⟩

/-- **The two conventions, related.**

Target typicality of `q` is source typicality of `q` against the *permuted* profile
`dwz63AlphaAddress ∘ cwSquarePermute e_o`.  A value lane that prefers source coordinates consumes
the right-hand side; the count lane consumes the left.  Since the six-fold symmetrized value is
invariant under permuting a component's legs, the two carry the same leaf weight. -/
theorem dwz63TargetTypical_iff_orientationTypical_comp (K : Type u) [CommRing K] (n t : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) :
    Dwz63TargetTypical K n t q ↔
      ∀ o : Fin 6, WordType.multiplicity (dwz63OrientedWord K n o q) =
        WordType.proportionalCounts
          (dwz63AlphaAddress ∘ cwSquarePermute (dwz63Orientation o)) t := by
  classical
  constructor
  · intro h o
    funext a
    have ha := congrFun (h o) (cwSquarePermute (dwz63Orientation o) a)
    rw [dwz63TargetWord_eq] at ha
    rw [multiplicity_comp_equiv] at ha
    simpa [WordType.proportionalCounts, Function.comp] using ha
  · intro h o
    funext a
    have ha := congrFun (h o) ((cwSquarePermute (dwz63Orientation o)).symm a)
    rw [dwz63TargetWord_eq, multiplicity_comp_equiv]
    simpa [WordType.proportionalCounts, Function.comp] using ha

/-- **The word length is forced**, exactly as in the source convention: `n + 1 = 10 ^ 8 * t`. -/
theorem dwz63TargetTypical_length {K : Type u} [CommRing K] {n t : ℕ}
    {q : PositiveWord ((dwz63SymSixPartition K).support) n}
    (h : Dwz63TargetTypical K n t q) : n + 1 = 100000000 * t := by
  have hsum := WordType.sum_multiplicity (dwz63TargetWord K n 0 q)
  rw [h 0] at hsum
  have hprofile : ∑ a : CWSquareAddress, WordType.proportionalCounts dwz63AlphaAddress t a =
      100000000 * t := by
    unfold WordType.proportionalCounts
    rw [← Finset.sum_mul]
    rw [show (∑ a : CWSquareAddress, dwz63AlphaAddress a) =
      WordType.profileMass dwz63AlphaAddress from rfl, profileMass_dwz63AlphaAddress]
  omega

/-- **The target-typical family**, the count lane's canonical `markedWords`. -/
noncomputable def dwz63TargetTypicalWords (K : Type u) [CommRing K] (n t : ℕ) :
    Finset (PositiveWord ((dwz63SymSixPartition K).support) n) := by
  classical
  exact Finset.univ.filter (Dwz63TargetTypical K n t)

theorem mem_dwz63TargetTypicalWords {K : Type u} [CommRing K] {n t : ℕ}
    {q : PositiveWord ((dwz63SymSixPartition K).support) n} :
    q ∈ dwz63TargetTypicalWords K n t ↔ Dwz63TargetTypical K n t q := by
  classical
  simp [dwz63TargetTypicalWords]

/-- Every subfamily of the target-typical family is target typical. -/
theorem targetTypical_of_subset {K : Type u} [CommRing K] {n t : ℕ}
    {markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n)}
    (hsub : markedWords ⊆ dwz63TargetTypicalWords K n t) :
    ∀ q ∈ markedWords, Dwz63TargetTypical K n t q :=
  fun _ hq ↦ mem_dwz63TargetTypicalWords.mp (hsub hq)

end AlgebraicComplexity.Examples
