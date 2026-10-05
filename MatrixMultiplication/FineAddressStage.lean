/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd
import AlgebraicComplexity.MatrixMultiplication.SingleConstituentStage
import MatrixMultiplication.SimplifiedSequencePackaging

set_option autoImplicit false

/-!
# The single-constituent fine-address stage of the total-weight stride block

## What this module is

`MatrixMultiplication/SimplifiedSequencePackaging.lean` closes its module documentation with an
honest gap: `WholeConstituentLaserVolumeSequenceData.volume_growth` carries **no** loss term, so it
is demanded at `r = 1` as well as asymptotically, whereas `RetainedCountValid` asks for the copy
count only *eventually* — below its cutoff it asks merely for `0 < count r`, and that cutoff is
existentially quantified in `TotalWeightTrackResidual`.

This module discharges the `r < cutoff` half of that asymmetry outright.  Below the cutoff a stage
may retain **one** constituent at a **single fine block address**, and then everything the
interface asks for is integer arithmetic.  Experiment **E2**
(`better_bound/r4_scoping/E2_LATTICE.md`, obligation **C1a**) named the address: the mass-`19`
integral profile at stride `38`, written here in **CW leg order** `(X, Y, Z)`,

| multiplicity | chunk class (one-type letters per leg, of `16`) |
|---|---|
| `9` | `(5, 5, 5)` plus one corner letter |
| `5` | `(5, 5, 6)` |
| `2` | `(6, 5, 5)` |
| `3` | `(5, 6, 5)` |

`19` chunks, `19 · 16 = 304` letters, `295` one-type letters and `9` corners, per-leg letter totals
`(97, 98, 100)` — the constants `xFineLetters`, `yFineLetters`, `zFineLetters` and
`cornerFineLetters` below, whose sum is `strideBlockLetters`.  Reading one `CW₅` letter at a
one-type block address gives the rectangular tensor `⟨5,1,1⟩`, `⟨1,5,1⟩` or `⟨1,1,5⟩` and at a
corner address `⟨1,1,1⟩`, so the whole address spells
`⟨5 ^ (97 r), 5 ^ (98 r), 5 ^ (100 r)⟩`.

## The leg convention (2026-08-28, C1b item 10)

E2 publishes this profile in the *certificate's* volume-coordinate order — multiplicities
`9 · (5,5,5)`, `5 · (6,5,5)`, `2 · (5,6,5)`, `3 · (5,5,6)` and totals `(100, 97, 98)` — and
certificate volume coordinate `c` is CW matrix-shape leg `(c + 2) % 3`
(`SimplifiedSequencePackaging.legOfCertificateCoordinate`).  The table and the constants above are
that profile **rotated into leg order**, so that they pair with the packaging's own per-leg budgets
`(225, 227, 232)`.

C1a's first landing recorded that a single fine address is convention-free, and *as an address*
that is true: the letters of one block address may be dealt out to the legs in any order, so
`cwStrideBlock_restricts_fineAddress` is provable for any permutation of `(97, 98, 100)`.  But the
**committed statements** were not convention-free, because they compose with the budgets:
`two_pow_yBudget_not_le_five_pow_xFineLetters` and
`two_pow_zBudget_not_le_five_pow_yFineLetters` below prove that two of the three comparisons are
*false* if the budgets are rotated and the letters are not.  So the rotation had to be inserted
here as well, and it is inserted exactly once — in the three constants.

## What it delivers

* `cwStrideBlock_restricts_fineAddress` — the exact restriction
  `(CW₅^⊗8)^⊗(38 r) ⊒ ⟨5^(97 r), 5^(98 r), 5^(100 r)⟩`, and `fineAddressStage`, the same fact as a
  `WholeConstituentLaserVolumeStage` of copy count `1`.
* `two_pow_xBudget_le_five_pow_xFineLetters` and its two siblings — the exact `ℕ` comparisons
  `2 ^ 225 ≤ 5 ^ 97`, `2 ^ 227 ≤ 5 ^ 98`, `2 ^ 232 ≤ 5 ^ 100`, proved the way the base-five
  predecessor `two_pow_le_leafBase_pow_budget` was proved before residual R3 retired it: `norm_num`
  on two exact numerals (`68`, `69` and `70` digits a side, well inside the default
  `exponentiation.threshold`).  Their slack is `0.227 / 0.549 / 0.193` bits, and the triple is
  tight: `5 ^ 96 < 2 ^ 225`, `5 ^ 97 < 2 ^ 227`, `5 ^ 99 < 2 ^ 232`.  These are the same three
  inequalities as before the leg rotation, re-paired to the legs.
* `two_pow_yBudget_not_le_five_pow_xFineLetters` and
  `two_pow_zBudget_not_le_five_pow_yFineLetters` — the two negative controls that make the rotation
  a *fact* rather than a taste: pair a budget with the neighbouring leg's letters and the
  comparison fails.
* `cwStrideBlock_restricts_leafBudget` and `leafBudgetStage` — the same stage in the packaging's own
  base-two coordinates `(leafBase ^ (225 r), leafBase ^ (227 r), leafBase ^ (232 r))`, which is
  literally the shape `RetainedExtractionValid` consumes.
* `belowCutoffStage` and `polynomialDegenerates_of_count_eq_one` — the per-repetition form a future
  `TotalWeightTrackResidual` witness cites in the branch where its count is `1`, and
  `retainedExtractionValid_countOne`, the whole extraction interface at the constant count `1`.

## What it deliberately does not do

* **It does not supply `RetainedCountValid`.**  A constant count `1` satisfies that predicate's
  positivity conjunct but not its copy floor `(2 ^ (38 · retained)) ^ r ≤ count r` above the
  cutoff.  Producing a count that grows is B-group counting work; this module only makes the
  *below*-cutoff branch free, so that the counting theorems never have to attain a rate at a finite
  repetition.
* **It is not C1b.**  E2's binding volume-side item is the zero-coordinate merge — a coarse address
  whose constituent is one `⟨1, 1, Σ_s 5 ^ ones s⟩` rather than a fine address of dimension
  `5 ^ ones s`.  The fine reading formalized here carries `637.586` bits per stride block against
  the `683.852` the milestone needs, so it is **not** on its own a route to `ω < 2.36999`: it is
  exactly and only the sub-cutoff discharge.  Nothing below claims otherwise.

No certificate table, no counting, no compatibility predicate and no partitioned tensor appears:
the address is spelled by `Tensor.Restricts.powerAdd_matrixMultiplication` over the three committed
`CW₅` block restrictions of `AlgebraicComplexity/Examples/CoppersmithWinograd.lean`.
-/

namespace MatrixMultiplication.FineAddressStage

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedSequencePackaging

universe u z

/-! ## The letter census of the fine address -/

/-- One-type letters of E2's mass-`19` profile that spend their factor `5` on the `X` leg.  E2
publishes this count at certificate volume coordinate `1`; see "The leg convention" above. -/
def xFineLetters : ℕ := 97

/-- One-type letters of E2's mass-`19` profile that spend their factor `5` on the `Y` leg.  E2
publishes this count at certificate volume coordinate `2`. -/
def yFineLetters : ℕ := 98

/-- One-type letters of E2's mass-`19` profile that spend their factor `5` on the `Z` leg.  E2
publishes this count at certificate volume coordinate `0`. -/
def zFineLetters : ℕ := 100

/-- Corner letters of E2's mass-`19` profile: one per `(5,5,5)` chunk, contributing `⟨1,1,1⟩`. -/
def cornerFineLetters : ℕ := 9

/-- The four letter classes exhaust the stride block's `304 = 8 · 38` letters. -/
theorem fineLetters_eq_strideBlockLetters :
    xFineLetters + yFineLetters + zFineLetters + cornerFineLetters = strideBlockLetters := by
  norm_num [xFineLetters, yFineLetters, zFineLetters, cornerFineLetters, strideBlockLetters]

/-- The one-type letter count of the address is `295` — the constant E2 identified as what
"volume `≥ 6` per word with `5`-power leaves" means on any route and at any stride. -/
theorem oneTypeFineLetters_eq :
    xFineLetters + yFineLetters + zFineLetters = 295 := by
  norm_num [xFineLetters, yFineLetters, zFineLetters]

/-! ## The three exact integer inequalities

Each per-leg bit budget of `SimplifiedSequencePackaging` is paid for by the corresponding power of
five, in CW leg order.  Both sides of every comparison have `68`, `69` or `70` decimal digits. -/

/-- **`2 ^ 225 ≤ 5 ^ 97`**, exactly — the `X` leg.  Slack `0.227` bits; `5 ^ 96 < 2 ^ 225`. -/
theorem two_pow_xBudget_le_five_pow_xFineLetters : (2 : ℕ) ^ 225 ≤ 5 ^ 97 := by norm_num

/-- **`2 ^ 227 ≤ 5 ^ 98`**, exactly — the `Y` leg.  Slack `0.549` bits; `5 ^ 97 < 2 ^ 227`. -/
theorem two_pow_yBudget_le_five_pow_yFineLetters : (2 : ℕ) ^ 227 ≤ 5 ^ 98 := by norm_num

/-- **`2 ^ 232 ≤ 5 ^ 100`**, exactly — the `Z` leg.  Slack `0.193` bits; `5 ^ 99 < 2 ^ 232`. -/
theorem two_pow_zBudget_le_five_pow_zFineLetters : (2 : ℕ) ^ 232 ≤ 5 ^ 100 := by norm_num

/-- **Negative control for the leg rotation, `Y` against `X`.**  `2 ^ 227 ≤ 5 ^ 97` is *false*: the
`Y` budget does not fit in the `X` leg's letters.  Together with its sibling this is what makes the
rotation of `xFineLetters`/`yFineLetters`/`zFineLetters` obligatory rather than cosmetic — had only
`SimplifiedSequencePackaging`'s budgets been rotated, `cwStrideBlock_restricts_leafBudget` would
have become unprovable, not merely differently spelled. -/
theorem two_pow_yBudget_not_le_five_pow_xFineLetters :
    ¬ (2 : ℕ) ^ yExponentBudget ≤ 5 ^ xFineLetters := by
  norm_num [yExponentBudget, xFineLetters]

/-- **Negative control for the leg rotation, `Z` against `Y`.**  `2 ^ 232 ≤ 5 ^ 98` is *false*. -/
theorem two_pow_zBudget_not_le_five_pow_yFineLetters :
    ¬ (2 : ℕ) ^ zExponentBudget ≤ 5 ^ yFineLetters := by
  norm_num [zExponentBudget, yFineLetters]

/-- The `X` budget at every repetition: exact powers are monotone, so one stride block's
comparison is the comparison at `r` stride blocks. -/
theorem leafBase_pow_xBudget_le_five_pow_xFineLetters (r : ℕ) :
    leafBase ^ (xExponentBudget * r) ≤ 5 ^ (xFineLetters * r) := by
  simp only [leafBase, xExponentBudget, xFineLetters, pow_mul]
  exact Nat.pow_le_pow_left two_pow_xBudget_le_five_pow_xFineLetters r

/-- The `Y` budget at every repetition. -/
theorem leafBase_pow_yBudget_le_five_pow_yFineLetters (r : ℕ) :
    leafBase ^ (yExponentBudget * r) ≤ 5 ^ (yFineLetters * r) := by
  simp only [leafBase, yExponentBudget, yFineLetters, pow_mul]
  exact Nat.pow_le_pow_left two_pow_yBudget_le_five_pow_yFineLetters r

/-- The `Z` budget at every repetition. -/
theorem leafBase_pow_zBudget_le_five_pow_zFineLetters (r : ℕ) :
    leafBase ^ (zExponentBudget * r) ≤ 5 ^ (zFineLetters * r) := by
  simp only [leafBase, zExponentBudget, zFineLetters, pow_mul]
  exact Nat.pow_le_pow_left two_pow_zBudget_le_five_pow_zFineLetters r

/-- The committed per-leg budgets are met exactly by the fine address's own exponents. -/
theorem leafExponentsValid_budget :
    LeafExponentsValid xExponentBudget yExponentBudget zExponentBudget
      xExponentBudget yExponentBudget zExponentBudget :=
  ⟨le_rfl, le_rfl, le_rfl⟩

/-! ## The four letterwise block restrictions -/

section Letters

variable (K : Type u) [CommSemiring K]

/-- A `CW₅` letter read at the `(1,0,1)` block address is `⟨5,1,1⟩`: its factor `5` is on `X`. -/
theorem cwFive_restricts_xLetter :
    Restricts (coppersmithWinograd K 5) (matrixMultiplication (K := K) 5 1 1) :=
  coppersmithWinograd_restricts_101 K 5

/-- A `CW₅` letter read at the `(1,1,0)` block address is `⟨1,5,1⟩`: its factor `5` is on `Y`. -/
theorem cwFive_restricts_yLetter :
    Restricts (coppersmithWinograd K 5) (matrixMultiplication (K := K) 1 5 1) :=
  coppersmithWinograd_restricts_110 K 5

/-- A `CW₅` letter read at the `(0,1,1)` block address is `⟨1,1,5⟩`: its factor `5` is on `Z`. -/
theorem cwFive_restricts_zLetter :
    Restricts (coppersmithWinograd K 5) (matrixMultiplication (K := K) 1 1 5) :=
  coppersmithWinograd_restricts_011 K 5

/-- A `CW₅` corner letter contributes nothing: `⟨1,1,1⟩`, obtained from the `(0,1,1)` block by
shrinking its `Z` dimension. -/
theorem cwFive_restricts_cornerLetter :
    Restricts (coppersmithWinograd K 5) (matrixMultiplication (K := K) 1 1 1) :=
  (coppersmithWinograd_restricts_011 K 5).trans
    (matrixMultiplication_restricts (K := K) le_rfl le_rfl (by norm_num))

end Letters

/-! ## The stride block at the fine address -/

section Stage

variable (K : Type u) [CommSemiring K]

/-- **The fine block address of E2's mass-`19` profile, as one exact restriction.**

`r` stride blocks are `304 · r` `CW₅` letters, split as `97 r` `X`-letters, `98 r` `Y`-letters,
`100 r` `Z`-letters and `9 r` corners; the address's constituent is the external product of the
corresponding rectangular blocks, whose three dimensions multiply.  No partition, no compatibility
cleanup and no counting is involved: this is a variable restriction at one block address. -/
theorem cwStrideBlock_restricts_fineAddress (r : ℕ) (hr : 0 < r) :
    Restricts
      (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
      (matrixMultiplication (K := K)
        (5 ^ (xFineLetters * r)) (5 ^ (yFineLetters * r)) (5 ^ (zFineLetters * r))) := by
  have hxpos : 0 < xFineLetters * r := Nat.mul_pos (by norm_num [xFineLetters]) hr
  have hypos : 0 < yFineLetters * r := Nat.mul_pos (by norm_num [yFineLetters]) hr
  have hzpos : 0 < zFineLetters * r := Nat.mul_pos (by norm_num [zFineLetters]) hr
  have hcpos : 0 < cornerFineLetters * r := Nat.mul_pos (by norm_num [cornerFineLetters]) hr
  have hX : Restricts (Tensor.power (coppersmithWinograd K 5) (xFineLetters * r))
      (matrixMultiplication (K := K) (5 ^ (xFineLetters * r)) 1 1) :=
    ((cwFive_restricts_xLetter K).power_matrixMultiplication hxpos).trans
      (Isomorphic.matrixMultiplication_congr (K := K) rfl (one_pow _) (one_pow _)).restricts
  have hY : Restricts (Tensor.power (coppersmithWinograd K 5) (yFineLetters * r))
      (matrixMultiplication (K := K) 1 (5 ^ (yFineLetters * r)) 1) :=
    ((cwFive_restricts_yLetter K).power_matrixMultiplication hypos).trans
      (Isomorphic.matrixMultiplication_congr (K := K) (one_pow _) rfl (one_pow _)).restricts
  have hZ : Restricts (Tensor.power (coppersmithWinograd K 5) (zFineLetters * r))
      (matrixMultiplication (K := K) 1 1 (5 ^ (zFineLetters * r))) :=
    ((cwFive_restricts_zLetter K).power_matrixMultiplication hzpos).trans
      (Isomorphic.matrixMultiplication_congr (K := K) (one_pow _) (one_pow _) rfl).restricts
  have hC : Restricts (Tensor.power (coppersmithWinograd K 5) (cornerFineLetters * r))
      (matrixMultiplication (K := K) 1 1 1) :=
    ((cwFive_restricts_cornerLetter K).power_matrixMultiplication hcpos).trans
      (Isomorphic.matrixMultiplication_congr (K := K)
        (one_pow _) (one_pow _) (one_pow _)).restricts
  have hZC := hZ.powerAdd_matrixMultiplication hC rfl (one_mul 1) (one_mul 1) (mul_one _)
  have hYZC := hY.powerAdd_matrixMultiplication hZC rfl (one_mul 1) (mul_one _) (one_mul _)
  have hXYZC := hX.powerAdd_matrixMultiplication hYZC rfl (mul_one _) (one_mul _) (one_mul _)
  refine Restricts.trans ?_ hXYZC
  refine ((Isomorphic.power_power (coppersmithWinograd K 5) 8 (strideValue * r)).trans
    (Isomorphic.power_congr (coppersmithWinograd K 5) ?_)).restricts
  simp only [strideValue, xFineLetters, yFineLetters, zFineLetters, cornerFineLetters]
  ring

/-- **The same stride block in the packaging's base-two coordinates.**  Each leg's power of five
dominates its bit budget, so the fine address also restricts onto
`⟨2 ^ (225 r), 2 ^ (227 r), 2 ^ (232 r)⟩` — literally the leaf shape `RetainedExtractionValid`
asks for. -/
theorem cwStrideBlock_restricts_leafBudget (r : ℕ) (hr : 0 < r) :
    Restricts
      (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
      (matrixMultiplication (K := K)
        (leafBase ^ (xExponentBudget * r)) (leafBase ^ (yExponentBudget * r))
        (leafBase ^ (zExponentBudget * r))) :=
  (cwStrideBlock_restricts_fineAddress K r hr).trans
    (matrixMultiplication_restricts (K := K)
      (leafBase_pow_xBudget_le_five_pow_xFineLetters r)
      (leafBase_pow_yBudget_le_five_pow_yFineLetters r)
      (leafBase_pow_zBudget_le_five_pow_zFineLetters r))

/-- **The single-constituent fine-address stage**, in the exact interface of
`WholeConstituentLaserVolumeSequenceData.stage`: one copy, side lengths
`(5 ^ (97 r), 5 ^ (98 r), 5 ^ (100 r))`. -/
noncomputable def fineAddressStage (r : ℕ) (hr : 0 < r) :
    WholeConstituentLaserVolumeStage.{u, u, z} K
      (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
      1 (5 ^ (xFineLetters * r)) (5 ^ (yFineLetters * r)) (5 ^ (zFineLetters * r)) :=
  WholeConstituentLaserVolumeStage.ofRestricts K (cwStrideBlock_restricts_fineAddress K r hr)

/-- The same stage at the committed per-leg bit budgets. -/
noncomputable def leafBudgetStage (r : ℕ) (hr : 0 < r) :
    WholeConstituentLaserVolumeStage.{u, u, z} K
      (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
      1 (leafBase ^ (xExponentBudget * r)) (leafBase ^ (yExponentBudget * r))
      (leafBase ^ (zExponentBudget * r)) :=
  WholeConstituentLaserVolumeStage.ofRestricts K (cwStrideBlock_restricts_leafBudget K r hr)

/-- **The below-cutoff branch, as a stage at a client's own count.**  Whenever a retained count is
`1` at a repetition — which is all `RetainedCountValid` demands below its cutoff — the stage at that
repetition is this one. -/
noncomputable def belowCutoffStage {count : ℕ → ℕ} {r : ℕ} (hr : 0 < r) (hcount : count r = 1) :
    WholeConstituentLaserVolumeStage.{u, u, z} K
      (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
      (count r) (leafBase ^ (xExponentBudget * r)) (leafBase ^ (yExponentBudget * r))
      (leafBase ^ (zExponentBudget * r)) := by
  rw [hcount]
  exact leafBudgetStage K r hr

end Stage

/-! ## What the packaging consumes -/

section Field

variable (K : Type u) [Field K]

/-- **The below-cutoff branch of `RetainedExtractionValid`, at one repetition.**  This is verbatim
the body of that predicate at `r`, so a witness that keeps its count at `1` below its cutoff cites
this and owes nothing further on the volume side there. -/
theorem polynomialDegenerates_of_count_eq_one {count : ℕ → ℕ} {r : ℕ}
    (hr : 0 < r) (hcount : count r = 1) :
    PolynomialDegenerates
      (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r))
      (matrixMultiplicationDirectSum (ι := Fin (count r)) K
        (fun _ ↦ leafBase ^ (xExponentBudget * r)) (fun _ ↦ leafBase ^ (yExponentBudget * r))
        (fun _ ↦ leafBase ^ (zExponentBudget * r))) :=
  (belowCutoffStage.{u, 0} K hr hcount).polynomialDegenerates

/-- **The whole extraction interface at the constant count `1`.**  Two of
`TotalWeightTrackResidual`'s three conjuncts are therefore available today at the committed
budgets: this one and `leafExponentsValid_budget`.  The third, `RetainedCountValid`, is *not*
satisfied by the constant count `1` above its cutoff, and supplying a count that grows is the
counting cone's obligation; what this theorem removes is any need for that cone to attain a rate at
a finite repetition. -/
theorem retainedExtractionValid_countOne :
    RetainedExtractionValid K (fun _ ↦ 1) xExponentBudget yExponentBudget zExponentBudget :=
  RetainedExtractionValid.of_stageFamily.{u, 0} fun r hr ↦ leafBudgetStage.{u, 0} K r hr

end Field

end MatrixMultiplication.FineAddressStage
