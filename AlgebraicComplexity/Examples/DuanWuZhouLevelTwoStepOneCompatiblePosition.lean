/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCompatible
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineConfigurationWitness

set_option autoImplicit false

/-!
# Reading one position, and one leg, of a Step-1 address

Layer 4 (`AlgebraicComplexity/Examples/`).  Three bookkeeping facts that the proof of the claim
`lemma:triple_implies_compatible` of `[duan2023faster]`, section 6.1 `sec:global-algo`
(`papers/sources/2210.10173/global_value.tex:63-71`), needs before its mathematics can run, plus
the fifteen-cell check that `dwz63Boundary` is the paper's boundary test.  The claim itself is
assembled in `Examples/DuanWuZhouLevelTwoStepOneCompatibleCut.lean`; nothing here is a statement of
the paper on its own.

* `dwz63_boundary_index_zero` --- `item:average` (`:48`) ranges over the large components with
  `i = 0` or `j = 0`; this is the check that the committed table `dwz63Boundary`
  (`Examples/DuanWuZhouLevelTwoCounting.lean:124`) is that test.
* `dwz63_fineLetterAddress_mem_cwSquareRawSupport` --- the paper's coordinatewise identity
  `Î + Ĵ + K̂ = (2^{ℓ-1}, …)` (`:70`) is a fact about one supported small cell, so a fine
  address
  must first be resolved into its per-position cells.
* `dwz63_cell_cellWordOfAddress` --- `:32` reads the large component `(I_t, J_t, K_t)` off the
  large triple; the large triple of a fine address is its coarsening, so the component is the
  degree-sum coarsening of that position's three fine letters.
* `dwz63_tripleOfLegWord_eq` --- `:55`'s "since `X_I` (if retained) is in a unique triple
  `(X_I, Y_J, Z_K)`", which is what makes the Step-1 `X̂`- and `Ŷ`-rules well defined.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:32-71`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

universe u

noncomputable section

variable {n : ℕ}

/-! ## `dwz63Boundary` is the paper's `i = 0 ∨ j = 0` (`global_value.tex:48`) -/

/-- **The boundary flag is `i = 0` or `j = 0`.**

`global_value.tex:48` restricts `item:average` to the large components with `i = 0` or `j = 0`;
`dwz63Boundary` (`Examples/DuanWuZhouLevelTwoCounting.lean:124`) is the committed table of that
test on the fifteen level-two components.  This is the fifteen-case check that the table says what
the paper says.

Proof sketch: exhaustive evaluation of three `Fin 15`-indexed vectors of `Fin 5` entries. -/
theorem dwz63_boundary_index_zero (t : Fin 15) (ht : dwz63Boundary t = true) :
    dwz63XIndex t = 0 ∨ dwz63YIndex t = 0 := by
  revert ht
  revert t
  decide

/-! ## Reading one position of a supported fine address -/

/-- **The three fine letters at one position form a supported raw square address.**

An address of the fine double power `dwz63FineDoublePower`
(`Examples/DuanWuZhouLevelTwoPreimageAmbient.lean:44`) is a word of supported level-one addresses,
transposed leg by leg; reading that word at a position returns a supported address of
`(cwPartitionedTensor K dwz63Q).positivePower 1`, whose support is `cwSquareRawSupport`.

This is the bookkeeping behind the paper's coordinatewise identity `Î + Ĵ + K̂ = 2^{ℓ-1}` at
`global_value.tex:70`: the identity is a fact about one supported small cell, so it can only be
used after the fine address has been resolved into its per-position cells.

Proof sketch: `exists_positiveSupportWord_of_mem_positivePower_support`
(`Tensor/PartitionedPower.lean:551`) produces the typed source word,
`positiveWordEquiv_positiveSupportWordBlockAddress` (`:215`) identifies its letters with the
transposed leg words, and `PartitionedTensor.mem_external_support`
(`Tensor/PartitionedProductCore.lean:82`) turns membership in the level-one power's support into
membership of both `CWBlock` projections in `cwBlockSupport`, which is `cwSquareRawSupport`
(`Examples/CoppersmithWinogradSquare.lean:81`). -/
theorem dwz63_fineLetterAddress_mem_cwSquareRawSupport (K : Type u) [CommRing K]
    (addr : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
    (hsup : addr ∈ (dwz63FineDoublePower K n).support) (i : Fin (n + 1)) :
    (fun c ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (addr c) i) ∈ cwSquareRawSupport := by
  classical
  obtain ⟨q, hq⟩ :=
    PartitionedTensor.exists_positiveSupportWord_of_mem_positivePower_support
      ((cwPartitionedTensor K dwz63Q).positivePower 1) n hsup
  set g : BlockAddress fun _ : Leg ↦ PositiveWord CWBlock 1 :=
    (positiveWordEquiv ((cwPartitionedTensor K dwz63Q).positivePower 1).support n q i).1 with hgdef
  have hproj : (fun c ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (addr c) i) = g := by
    funext c
    have h := positiveWordEquiv_positiveSupportWordBlockAddress
      ((cwPartitionedTensor K dwz63Q).positivePower 1).support n q c
    rw [congrFun hq c] at h
    exact congrFun h i
  have hmem : g ∈ ((cwPartitionedTensor K dwz63Q).positivePower 1).support :=
    (positiveWordEquiv ((cwPartitionedTensor K dwz63Q).positivePower 1).support n q i).2
  have hparts := (PartitionedTensor.mem_external_support
    ((cwPartitionedTensor K dwz63Q).positivePower 0) (cwPartitionedTensor K dwz63Q) g).mp hmem
  rw [hproj]
  exact Finset.mem_map.mpr
    ⟨((fun c ↦ (g c).1), (fun c ↦ (g c).2)),
      Finset.mem_product.mpr ⟨hparts.1, hparts.2⟩, rfl⟩

/-- **The large component of a position is the coarse cell of its fine letters.**

`global_value.tex:32` reads the component `(I_t, J_t, K_t)` off the large triple; the large triple
of a fine address is its coarsening, so at every position the component is the degree-sum
coarsening of that position's three fine letters.  Stated through `dwz63Cell`, this delivers all
three coordinates at once: evaluating at `Leg.X`, `Leg.Y`, `Leg.Z` gives `dwz63XIndex`,
`dwz63YIndex`, `dwz63ZIndex` of the component.

Proof sketch: image 139's `dwz63_coarseDegree_at_position` rewrites the coarse letter at each leg
as the square degree of the fine letter, and `dwz63Cell_dwz63CellIndex`
(`Examples/DuanWuZhouLevelTwoFineConfigurationWitness.lean:125`) inverts `dwz63CellIndex` on the
coarse support, which the position's cell belongs to by the previous lemma. -/
theorem dwz63_cell_cellWordOfAddress (K : Type u) [CommRing K]
    (addr : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
    (hsup : addr ∈ (dwz63FineDoublePower K n).support) (i : Fin (n + 1)) :
    dwz63Cell
        (dwz63CellWordOfAddress
          (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr) i) =
      coarsenBlockAddress cwSquareDegreeMap
        (fun c ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (addr c) i) := by
  classical
  have hraw := dwz63_fineLetterAddress_mem_cwSquareRawSupport K addr hsup i
  have hcoarse :
      (fun c ↦ positiveWordEquiv (Fin 5) n
          (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr c) i) =
        coarsenBlockAddress cwSquareDegreeMap
          (fun c ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (addr c) i) := by
    funext c
    exact dwz63_coarseDegree_at_position addr c i
  have hmem : coarsenBlockAddress cwSquareDegreeMap
      (fun c ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (addr c) i) ∈ cwSquareSupport :=
    Finset.mem_image_of_mem _ hraw
  show dwz63Cell (dwz63CellIndex (fun c ↦ positiveWordEquiv (Fin 5) n
      (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr c) i)) = _
  rw [hcoarse]
  exact dwz63Cell_dwz63CellIndex hmem

/-! ## "`X_I` (if retained) is in a unique triple" (`global_value.tex:55`) -/

/-- **The Step-1 leg lookup returns the retained triple that carries the leg word.**

`global_value.tex:55` justifies defining `S_{i,j,k}` from a small `X`-block by "since `X_I` (if
retained) is in a unique triple `(X_I, Y_J, Z_K)`".  `dwz63TripleOfLegWord`
(`Examples/DuanWuZhouLevelTwoStepOneKeep.lean:55`) is that lookup as a `dite`; the paper's
uniqueness is the hypothesis `hinj`, the hash's leg-injectivity certificate on the retained family
(the same `Set.InjOn` shape the committed `dwz63PlainCoarseGroup_eq_of_x`
(`Examples/DuanWuZhouLevelTwoPlainGroupedStage.lean:111`) takes).

Proof sketch: the supplied `a` is a witness, so the `dite` takes its positive branch; injectivity
then identifies the chosen witness with `a`. -/
theorem dwz63_tripleOfLegWord_eq
    {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)} (a₀ : retained)
    (c₀ : Leg)
    (hinj : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g c₀)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    {lw : PositiveWord (Fin 5) n} {a : retained}
    (ha : (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c₀ = lw) :
    dwz63TripleOfLegWord retained a₀ c₀ lw = a := by
  classical
  have hex : ∃ g : retained,
      (g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c₀ = lw := ⟨a, ha⟩
  unfold dwz63TripleOfLegWord
  rw [dif_pos hex]
  refine Subtype.ext (hinj hex.choose.2 a.2 ?_)
  show (hex.choose : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c₀ =
    (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c₀
  rw [hex.choose_spec, ha]

end

end AlgebraicComplexity.Examples
