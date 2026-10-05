/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentationData

set_option autoImplicit false

/-!
# The reference word of the section 6.3 assembly

Layer 4 (`AlgebraicComplexity/Examples/`).  The localized stage of `[duan2023faster]` §6.3
identifies every retained copy with one **reference leaf**, built from a reference word `wRef`
whose fifteen coarse cells carry the prescribed masses

`multiplicity (dwz63Seg K n wRef) t = 2 * 10 ^ 8 * (dwz63Alpha t * s)`.

This module produces it.  There is no choice involved and no interaction with the *fine* letters:
`wRef` is a word over the **coarse** level-two alphabet, which is the fifteen-address support
`cwSquareSupport` (`card_cwSquareSupport`), and `dwz63CellEquiv : Fin 15 ≃ CWSquareSupport`
(`Examples/DuanWuZhouLevelTwoSupportBridge.lean:133`) already identifies that alphabet with the
component index.  So the required cell profile *is* a letter profile, and the word is the transport
of any `Fin 15`-word of that type.

The fine letters --- the ones the split distribution `dwz63AlphaTilde` constrains --- live in
`SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s)`, not in `wRef`, so nothing
here interacts with the availability count.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3 and `table:result-2nd`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/global_value.tex:354-378` (`table:result-2nd`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-- **The reference word exists, at every joined period.**

`n + 1 = 2 * 10 ^ 16 * s` is the total mass `∑ t, 2 * 10 ^ 8 * (dwz63Alpha t * s)`, using
`∑ t, dwz63Alpha t = 10 ^ 8`.  This discharges the `R2` binder of the section 6.3 assembly. -/
theorem dwz63_exists_referenceWord (K : Type u) [CommRing K] (n s : ℕ)
    (hn : n + 1 = 20000000000000000 * s) :
    ∃ wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n,
      ∀ t : Fin 15,
        WordType.multiplicity (dwz63Seg K n wRef) t = 200000000 * (dwz63Alpha t * s) := by
  classical
  have halpha : ∑ t : Fin 15, dwz63Alpha t = 100000000 := profileMass_dwz63Alpha
  have hmass : ∑ t : Fin 15, 200000000 * (dwz63Alpha t * s) = n + 1 := by
    have h1 : ∑ t : Fin 15, 200000000 * (dwz63Alpha t * s)
        = 200000000 * s * ∑ t : Fin 15, dwz63Alpha t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ ↦ by ring
    rw [h1, halpha, hn]
    ring
  obtain ⟨w15, hw15mem⟩ :=
    WordType.typeClass_nonempty (fun t : Fin 15 ↦ 200000000 * (dwz63Alpha t * s))
      (WordType.mem_types.2 hmass)
  have hw15 : WordType.multiplicity w15 = fun t : Fin 15 ↦ 200000000 * (dwz63Alpha t * s) :=
    WordType.mem_typeClass.mp hw15mem
  obtain ⟨wRef, hwRef⟩ :=
    (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n).surjective
      (fun i ↦ dwz63CellEquiv (w15 i))
  refine ⟨wRef, fun t ↦ ?_⟩
  have hseg : dwz63Seg K n wRef = w15 := by
    funext i
    unfold dwz63Seg
    rw [hwRef]
    simp
  rw [hseg, hw15]

end AlgebraicComplexity.Examples
