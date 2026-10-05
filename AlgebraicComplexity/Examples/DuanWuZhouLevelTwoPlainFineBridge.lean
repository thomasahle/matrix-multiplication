/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainGroupedStage

set_option autoImplicit false

/-!
# The plain power reaches the fine double power, and what it does **not** reach

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoGroupedLeaf.lean`'s
`dwz63_groupedStage_of_claim3` carries

`hfine : Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n+1))
           (dwz63PlainFine K n retained a₀ holesFine).realize`.

Its first two steps are unconditional and are proved here.  Its third step is **not provable as
stated**, and the obstruction is structural; see below.

## The two steps that work

`cwSquarePartitionedTensor K q` is by definition
`((cwPartitionedTensor K q).positivePower 1).coarsen cwSquareDegreeMap`, and coarsening a
partition does not change the realized tensor --- `cwSquare_coarsening_isomorphic`
(`Examples/CoppersmithWinogradSquare.lean:317`).  So the coarse power *is* the raw power, and
`Tensor.Restricts.power_partitionedPositivePower` opens it as the fine double power.  That is
`dwz63_power_restricts_finePower`, and `dwz63_power_restricts_fineSelect` adds any legwise cut by
`Tensor.Restricts.partitionedSelect`.

## Why `dwz63PlainFine` itself is not reachable by zeroing

`dwz63PlainFine`'s support keeps a fine address `s` exactly when **all three** of its coarse leg
words point at the *same* retained triple --- `∀ c, (group s) c = coarse c (s c)`, with
`group` reading `s .X` alone --- and `s .Z` is not a hole for it.  A `Restricts` onto a
`withSupport` is a legwise variable zero-out, so it must satisfy `IsProjectionClosed`: if the three
labels `s .X`, `s .Y`, `s .Z` each occur in the kept family, then `s` itself must be kept.  That
fails here, and it fails for the reason the construction exists: take retained `a ≠ b`, a kept
address `u` over `a` and a kept address `v` over `b`, and assemble `s` with `s .X = u .X`,
`s .Y = v .Y`.  Every label of `s` is a kept label, but `group s = a` while
`coarse .Y (s .Y) = b .Y ≠ a .Y`, so `s` is **crossed** and is not in `dwz63PlainFine`'s support.
Uncrossing is exactly what a legwise zero-out cannot do.

## The repoint this suggests

Uncrossing is free in the *grouped* framework, and needs no hypothesis at all.  Taking the
compatibility relation to be equality of the pivot label,
`compatible y s := (s pivot = y)`, soundness is `rfl`
(`dwz63_isCompatibilitySound_selfLabel`), and
`Tensor.Restricts.partitionedGroupCompatibilityIsolated` deletes precisely the labels shared by two
coarse groups.  `dwz63_restricts_groupLabelIsolated` is that step, and
`groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers` says the survivors read their group off
that leg --- which is `dwz63_plainGroupedBrokenDirectSum`'s `hcover` obligation in the form it
actually needs.

So the reachable ambient is

`fine power` → legwise `select` on coarse-word membership → group-label isolation at `.Y` → at
`.Z`,

all four steps committed and hypothesis-free, and `dwz63PlainFine` should be replaced by that
object.  What then has to be re-proved is `hcover`/`hambient` for it, in place of `hfine`.  That is
a strictly better trade: `hfine` is false-as-stated, whereas `hcover` after the `.Y` isolation is
exactly what group-label isolation delivers.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w x

/-! ## The coarse power is the fine double power -/

/-- **The plain power opens as the fine double power.**  Coarsening does not move the realized
tensor, so the fifteen-block square power *is* the raw square's double power. -/
theorem dwz63_power_restricts_finePower (K : Type u) [CommRing K] (n : ℕ) :
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      ((((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).realize) :=
  ((cwSquare_coarsening_isomorphic K dwz63Q).symm.power (n + 1)).restricts.trans
    (Tensor.Restricts.power_partitionedPositivePower
      ((cwPartitionedTensor K dwz63Q).positivePower 1) n)

/-- **Any legwise cut of the fine double power is reachable from the plain power.** -/
theorem dwz63_power_restricts_fineSelect (K : Type u) [CommRing K] (n : ℕ)
    (keep : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop)
    [∀ c w, Decidable (keep c w)] :
    Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (n + 1))
      (((((cwPartitionedTensor K dwz63Q).positivePower 1).positivePower n).select keep).realize) :=
  (dwz63_power_restricts_finePower K n).trans
    (Tensor.Restricts.partitionedSelect _ keep)

/-! ## Uncrossing is free -/

section Uncross

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {Γ : Type x}

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- **Equality of the pivot label is a sound compatibility relation**, with no hypothesis.  This is
the instance that makes group-label isolation --- the uncrossing step --- free. -/
theorem dwz63_isCompatibilitySound_selfLabel (ambient : Finset (BlockAddress A)) (pivot : Leg) :
    IsCompatibilitySound ambient pivot (fun label address ↦ address pivot = label) :=
  fun _ _ ↦ rfl

/-- **Uncrossing at one leg, as an exact restriction.**

Deleting every `pivot` label shared by two coarse groups is a genuine variable zero-out, and the
survivors read their group off that label.  No hypothesis: the compatibility relation is equality
of the label. -/
theorem dwz63_restricts_groupLabelIsolated
    (P : PartitionedTensor (K := K) (A := A) V) (group : BlockAddress A → Γ) (pivot : Leg) :
    Restricts P.realize
      (P.withSupport
        (groupCompatibilityIsolatedSupport P.support group pivot
          (fun label address ↦ address pivot = label))).realize :=
  Tensor.Restricts.partitionedGroupCompatibilityIsolated P group pivot _
    (dwz63_isCompatibilitySound_selfLabel P.support pivot)

/-- **The survivors read their group off the isolated leg.**  This is `hcover`'s content, in the
form group-label isolation delivers it. -/
theorem dwz63_groupLabelIsolated_hasGroupUniqueLegFibers
    (P : PartitionedTensor (K := K) (A := A) V) (group : BlockAddress A → Γ) (pivot : Leg) :
    HasGroupUniqueLegFibers P.support
      (groupCompatibilityIsolatedSupport P.support group pivot
        (fun label address ↦ address pivot = label)) group pivot :=
  groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers P.support group pivot _
    (dwz63_isCompatibilitySound_selfLabel P.support pivot)

end Uncross

end AlgebraicComplexity.Examples
