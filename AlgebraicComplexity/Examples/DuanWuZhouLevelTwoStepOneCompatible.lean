/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneKeep
import AlgebraicComplexity.MatrixMultiplication.SegmentMultiplicityReflect

set_option autoImplicit false

/-!
# The inputs of `lemma:triple_implies_compatible`

Layer 4 (`AlgebraicComplexity/Examples/`).  This module carries the **letter-level inputs** of the
claim `lemma:triple_implies_compatible` of `[duan2023faster]`
(`papers/sources/2210.10173/global_value.tex:63-71`).  The assembled claim --- every address of
`dwz63FineStepOneCut` is `(dwz63SplitPair s).IsCompatible` with the cell word of its own retained
triple --- is **not** proved here; see the note at the end of this docstring.

The claim reads:

>  After Additional Zeroing-Out Step 1, a remaining small block `Z_K̂ ∈ Z_K` can form a triple
> with
>  remaining `X_Î ∈ X_I`, `Y_Ĵ ∈ Y_J` only when `Z_K̂` is compatible with triple `(X_I, Y_J,
> Z_K)`.

"Can form a triple with remaining `X_Î`, `Y_Ĵ`" is, in the tensor spelling, membership of the
whole
fine address in `dwz63FineStepOneCut` --- all three legs survive Step 1 --- and "compatible" is
`def:global-compatible` (`:44-50`), which the tree transcribes as
`SplitRequirements.IsCompatible = BoundaryMatched ∧ IsTypical`
(`Combinatorics/CompatibleSplitCountDefs.lean:117,126`).

## The paper's proof, in its order

`:67` "first notice that after Additional Zeroing-Out Step 1, all `Z_K̂` that are not zeroed out
satisfy `item:split-match`" --- that is the `.Z` conjunct of `dwz63FineStepOneKeep`, and it gives
the `IsTypical` half directly, once the large `Z`-index word of the triple is identified with the
degree word read off the fine `Z`-word (`dwz63_coarseDegree_at_position`).

`:67` "Hence, if `Z_K̂` is not compatible … it must be that for some `(i,j,k)` with `i = 0` or
`j = 0`, `split(K̂, S_{i,j,k}) ≠ splres_{i,j,k}` (`item:average`)" --- so what remains is
`BoundaryMatched`, on exactly the cells `dwz63Boundary` marks.

`:70` "Due to symmetry, we only have to discuss the case where `j = 0`.  By our zeroing-out rules,
we know that `split(Î, S_{i,0,k}) = splres^{(X)}_{i,0,k}`.  As `j = 0` and
`Î + Ĵ + K̂ = (2^{ℓ-1}, …, 2^{ℓ-1})`, we necessarily have that
`split(K̂, S_{i,0,k})(k') = split(Î, S_{i,0,k})(2^{ℓ-1} - k') = splres^{(X)}_{i,0,k}(2^{ℓ-1} -
k')
= splres_{i,0,k}(k')`."

At level two that chain is: the fine `Y`-letter at a `j = 0` position has square degree zero, so
both its `CWBlock` digits are `zero` and `Î_s = 2 - K̂_s` on both digits
(`cwBlock_eq_complement_of_zeroY`, image 137) --- i.e. the fine `X`-letter is
`cwSquareComplementLetter` of the fine `Z`-letter; the distribution then reflects along that
involution (`segmentMultiplicity_comp_involutive`), and `splres^{(X)}` is by definition
`splres` reflected (`dwz63SplresReflected`, `:56`).  The paper's "due to symmetry" is the `i = 0`
half, which needs the mirror letter fact `cwBlock_eq_complement_of_zeroX`; image 137 states only
the `j = 0` one, so the mirror is proved here.

## What is here, and what is not

Here: the `i = 0` mirror letter fact (`cwBlock_eq_complement_of_zeroX`,
`cwSquare_fineY_eq_complement_of_zeroX`), the involutivity of the level-two reflection
(`cwSquareComplementLetter_involutive`), and the identification of the large index word with the
degree word of the fine word (`dwz63_coarseDegree_at_position`, `global_value.tex:32`).  Together
with image 137's `j = 0` fact and the generic
`segmentMultiplicity_comp_involutive` these are exactly the inputs of the displayed chain at `:70`,
and that chain is assembled from them in this increment's composition test.

Not here: the assembled claim.  What it still needs is bookkeeping, not new mathematics --- the
extraction of the level-one supported address at each position from membership in the fine double
power, the identification of `dwz63TripleOfLegWord`'s lookup with the address's own coarsening
under the hash's `hX`/`hY`, and the `multiplicity (jointWord …)` versus `segmentMultiplicity`
spelling of `BoundaryMatched`.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`global_value.tex:32, 44-50,
63-71`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

universe u

/-! ## The mirror of image 137's letter fact (`global_value.tex:70`, "due to symmetry") -/

/-- **On a supported address with `X`-letter `zero`, the `Y`-letter is the complement of the
`Z`-letter.**  The `i = 0` half of the paper's symmetry remark at `global_value.tex:70`. -/
theorem cwBlock_eq_complement_of_zeroX (y z : CWBlock)
    (h : cwBlockAddress CWBlock.zero y z ∈ cwBlockSupport) :
    y = cwBlockComplement z := by
  rw [mem_cwBlockSupport_ofLegs] at h
  refine cwBlockDegree_injective ?_
  have hc := cwBlockDegree_cwBlockComplement z
  cases z <;> cases y <;> simp_all [cwBlockDegree, cwBlockComplement]

/-- **The letterwise complement is an involution.**  `2 - (2 - d) = d`. -/
theorem cwSquareComplementLetter_involutive :
    Function.Involutive cwSquareComplementLetter := by
  rintro ⟨a, b⟩
  have ha : cwBlockComplement (cwBlockComplement a) = a := by cases a <;> rfl
  have hb : cwBlockComplement (cwBlockComplement b) = b := by cases b <;> rfl
  exact Prod.ext ha hb

/-- **On a supported raw square address with `X`-letter of degree zero, the `Y`-letter is the
letterwise complement of the `Z`-letter.**  The mirror of image 137's
`cwSquare_fineX_eq_complement_of_zeroY`. -/
theorem cwSquare_fineY_eq_complement_of_zeroX
    (f : BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1))
    (hf : f ∈ cwSquareRawSupport) (hX : cwSquareBlockDegree (f Leg.X) = 0) :
    f Leg.Y = cwSquareComplementLetter (f Leg.Z) := by
  classical
  obtain ⟨q, hq, hqf⟩ := Finset.mem_map.mp hf
  obtain ⟨b₁, b₂⟩ := q
  obtain ⟨hb₁, hb₂⟩ := Finset.mem_product.mp hq
  have hfX : f Leg.X = (b₁ Leg.X, b₂ Leg.X) := by rw [← hqf]; rfl
  have hfY : f Leg.Y = (b₁ Leg.Y, b₂ Leg.Y) := by rw [← hqf]; rfl
  have hfZ : f Leg.Z = (b₁ Leg.Z, b₂ Leg.Z) := by rw [← hqf]; rfl
  have hx : cwBlockDegree (b₁ Leg.X) + cwBlockDegree (b₂ Leg.X) = 0 := by
    have := hX
    rw [hfX] at this
    simpa [cwSquareBlockDegree, Fin.ext_iff] using this
  have hx₁ : b₁ Leg.X = CWBlock.zero := by
    refine cwBlockDegree_injective ?_
    have : cwBlockDegree (b₁ Leg.X) = 0 := by omega
    simpa [cwBlockDegree] using this
  have hx₂ : b₂ Leg.X = CWBlock.zero := by
    refine cwBlockDegree_injective ?_
    have : cwBlockDegree (b₂ Leg.X) = 0 := by omega
    simpa [cwBlockDegree] using this
  have hmem₁ : cwBlockAddress CWBlock.zero (b₁ Leg.Y) (b₁ Leg.Z) ∈ cwBlockSupport := by
    have hb : cwBlockAddress (b₁ Leg.X) (b₁ Leg.Y) (b₁ Leg.Z) = b₁ := by
      funext c; cases c <;> rfl
    rw [← hx₁, hb]
    exact hb₁
  have hmem₂ : cwBlockAddress CWBlock.zero (b₂ Leg.Y) (b₂ Leg.Z) ∈ cwBlockSupport := by
    have hb : cwBlockAddress (b₂ Leg.X) (b₂ Leg.Y) (b₂ Leg.Z) = b₂ := by
      funext c; cases c <;> rfl
    rw [← hx₂, hb]
    exact hb₂
  rw [hfY, hfZ]
  exact Prod.ext (cwBlock_eq_complement_of_zeroX _ _ hmem₁)
    (cwBlock_eq_complement_of_zeroX _ _ hmem₂)

/-! ## Reading the large triple off the fine address (`global_value.tex:32`) -/

section Position

variable {n : ℕ} {K : Type u} [CommRing K]

/-- **The large index word is the degree word of the fine word**, position by position.

`global_value.tex:32` reads `(I_t, J_t, K_t)` off the large triple; the large triple of a fine
address is its coarsening, so at every position the large letter on leg `c` is the square degree of
the fine letter there. -/
theorem dwz63_coarseDegree_at_position
    (addr : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
    (c : Leg) (i : Fin (n + 1)) :
    positiveWordEquiv (Fin 5) n
        ((coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr) c) i =
      cwSquareBlockDegree (positiveWordEquiv (PositiveWord CWBlock 1) n (addr c) i) := by
  show positiveWordEquiv (Fin 5) n (positiveWordMap (cwSquareDegreeMap c) n (addr c)) i = _
  rw [positiveWordEquiv_map]
  rfl

end Position

end AlgebraicComplexity.Examples
