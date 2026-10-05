/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TernaryEncoding
import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricProfile
import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerHashing

/-!
# Affine-hashing labels for the symmetric CW `112` support

The modern `112` value proof hashes the product of the constituent with its two cyclic
orientations as one ordinary three-legged partition.  A visible block on each leg is therefore
a triple of primitive CW block labels.  This file packs those three labels into one base-three
integer and proves that the resulting labels form a legal constant-sum hashing support.

The construction is structural.  Primitive CW labels lie in `{0,1,2}` and every primitive
support address has label sum two.  Giving the three oriented source factors radix weights
`1`, `3`, and `9` makes every symmetric support address have label sum

`2 * (1 + 3 + 9) = 26`.

Consequently any prime field of cardinality at least `27` provides injective block labels.  No
enumeration of the 64 supported symmetric addresses is used.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Natural representatives of the primitive CW tight-support labels.

The X and Y labels are `0,1`; the Z labels are `2,0,1`.  This is the natural-number version of
`cw112BlockFieldValue`, kept separate so compound encodings can first be proved injective before
being cast into a finite field. -/
def cw112BlockNatValue : ∀ c, CW112Block c → ℕ
  | .X, .first => 0
  | .X, .second => 1
  | .Y, .first => 0
  | .Y, .second => 1
  | .Z, .firstCorner => 2
  | .Z, .secondCorner => 0
  | .Z, .grid => 1

/-- Every primitive CW block label is a ternary digit. -/
theorem cw112BlockNatValue_lt_three (c : Leg) (block : CW112Block c) :
    cw112BlockNatValue c block < 3 := by
  cases c <;> cases block <;> decide

/-- Natural primitive CW block labels are injective on every leg. -/
theorem cw112BlockNatValue_injective (c : Leg) :
    Function.Injective (cw112BlockNatValue c) := by
  cases c <;> intro left right h <;>
    cases left <;> cases right <;> simp_all [cw112BlockNatValue]

/-- Every primitive supported address has total natural label two.

Proof sketch: the four support addresses are respectively labelled `(0,0,2)`, `(1,1,0)`,
`(0,1,1)`, and `(1,0,1)`. -/
theorem cw112BlockNatValue_legal
    (address : BlockAddress CW112Block) (haddress : address ∈ cw112BlockSupport) :
    cw112BlockNatValue .X (address .X) +
        cw112BlockNatValue .Y (address .Y) +
        cw112BlockNatValue .Z (address .Z) = 2 := by
  simp only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl <;>
    decide

/-- Base-three label of one compound block in the three-orientation product.

The digits consistently correspond to the unpermuted, cyclic, and inverse-cyclic source
factors, even though their primitive tensor legs differ on each visible output leg. -/
def cw112SymmetricBlockNatValue : ∀ c, CW112SymmetricBlock c → ℕ
  | .X, ((x, z), y) =>
      ternaryTripleCode
        (cw112BlockNatValue .X x)
        (cw112BlockNatValue .Z z)
        (cw112BlockNatValue .Y y)
  | .Y, ((y, x), z) =>
      ternaryTripleCode
        (cw112BlockNatValue .Y y)
        (cw112BlockNatValue .X x)
        (cw112BlockNatValue .Z z)
  | .Z, ((z, y), x) =>
      ternaryTripleCode
        (cw112BlockNatValue .Z z)
        (cw112BlockNatValue .Y y)
        (cw112BlockNatValue .X x)

/-- Every compound label lies in the interval `[0,27)`. -/
theorem cw112SymmetricBlockNatValue_lt
    (c : Leg) (block : CW112SymmetricBlock c) :
    cw112SymmetricBlockNatValue c block < 27 := by
  cases c with
  | X =>
      rcases block with ⟨⟨x, z⟩, y⟩
      exact ternaryTripleCode_lt
        (cw112BlockNatValue_lt_three .X x)
        (cw112BlockNatValue_lt_three .Z z)
        (cw112BlockNatValue_lt_three .Y y)
  | Y =>
      rcases block with ⟨⟨y, x⟩, z⟩
      exact ternaryTripleCode_lt
        (cw112BlockNatValue_lt_three .Y y)
        (cw112BlockNatValue_lt_three .X x)
        (cw112BlockNatValue_lt_three .Z z)
  | Z =>
      rcases block with ⟨⟨z, y⟩, x⟩
      exact ternaryTripleCode_lt
        (cw112BlockNatValue_lt_three .Z z)
        (cw112BlockNatValue_lt_three .Y y)
        (cw112BlockNatValue_lt_three .X x)

/-- Compound natural labels are injective on each symmetric tensor leg.

Proof sketch: equality of the packed base-three values recovers all three primitive digits;
injectivity of the primitive CW labels then recovers the three block labels. -/
theorem cw112SymmetricBlockNatValue_injective (c : Leg) :
    Function.Injective (cw112SymmetricBlockNatValue c) := by
  intro left right h
  cases c with
  | X =>
      rcases left with ⟨⟨lx, lz⟩, ly⟩
      rcases right with ⟨⟨rx, rz⟩, ry⟩
      obtain ⟨hx, hz, hy⟩ := ternaryTripleCode_injectiveOn
        (cw112BlockNatValue_lt_three .X lx)
        (cw112BlockNatValue_lt_three .Z lz)
        (cw112BlockNatValue_lt_three .Y ly)
        (cw112BlockNatValue_lt_three .X rx)
        (cw112BlockNatValue_lt_three .Z rz)
        (cw112BlockNatValue_lt_three .Y ry) h
      exact Prod.ext
        (Prod.ext (cw112BlockNatValue_injective .X hx)
          (cw112BlockNatValue_injective .Z hz))
        (cw112BlockNatValue_injective .Y hy)
  | Y =>
      rcases left with ⟨⟨ly, lx⟩, lz⟩
      rcases right with ⟨⟨ry, rx⟩, rz⟩
      obtain ⟨hy, hx, hz⟩ := ternaryTripleCode_injectiveOn
        (cw112BlockNatValue_lt_three .Y ly)
        (cw112BlockNatValue_lt_three .X lx)
        (cw112BlockNatValue_lt_three .Z lz)
        (cw112BlockNatValue_lt_three .Y ry)
        (cw112BlockNatValue_lt_three .X rx)
        (cw112BlockNatValue_lt_three .Z rz) h
      exact Prod.ext
        (Prod.ext (cw112BlockNatValue_injective .Y hy)
          (cw112BlockNatValue_injective .X hx))
        (cw112BlockNatValue_injective .Z hz)
  | Z =>
      rcases left with ⟨⟨lz, ly⟩, lx⟩
      rcases right with ⟨⟨rz, ry⟩, rx⟩
      obtain ⟨hz, hy, hx⟩ := ternaryTripleCode_injectiveOn
        (cw112BlockNatValue_lt_three .Z lz)
        (cw112BlockNatValue_lt_three .Y ly)
        (cw112BlockNatValue_lt_three .X lx)
        (cw112BlockNatValue_lt_three .Z rz)
        (cw112BlockNatValue_lt_three .Y ry)
        (cw112BlockNatValue_lt_three .X rx) h
      exact Prod.ext
        (Prod.ext (cw112BlockNatValue_injective .Z hz)
          (cw112BlockNatValue_injective .Y hy))
        (cw112BlockNatValue_injective .X hx)

/-- The compound labels of an assembled symmetric source triple sum to `26`.

Proof sketch: regroup by source orientation.  The first, second, and third primitive addresses
contribute their constant sums with coefficients `1`, `3`, and `9`, respectively, hence the
total is `2 + 3·2 + 9·2 = 26`. -/
theorem cw112SymmetricBlockNatValue_address_sum (source : CW112SourceTriple) :
    cw112SymmetricBlockNatValue .X (cw112SymmetricAddress source .X) +
        cw112SymmetricBlockNatValue .Y (cw112SymmetricAddress source .Y) +
        cw112SymmetricBlockNatValue .Z (cw112SymmetricAddress source .Z) = 26 := by
  have hfirst := cw112BlockNatValue_legal source.1.1.1 source.1.1.2
  have hsecond := cw112BlockNatValue_legal source.1.2.1 source.1.2.2
  have hthird := cw112BlockNatValue_legal source.2.1 source.2.2
  change ternaryTripleCode
        (cw112BlockNatValue .X (source.1.1.1 .X))
        (cw112BlockNatValue .Z (source.1.2.1 .Z))
        (cw112BlockNatValue .Y (source.2.1 .Y)) +
      ternaryTripleCode
        (cw112BlockNatValue .Y (source.1.1.1 .Y))
        (cw112BlockNatValue .X (source.1.2.1 .X))
        (cw112BlockNatValue .Z (source.2.1 .Z)) +
      ternaryTripleCode
        (cw112BlockNatValue .Z (source.1.1.1 .Z))
        (cw112BlockNatValue .Y (source.1.2.1 .Y))
        (cw112BlockNatValue .X (source.2.1 .X)) = 26
  unfold ternaryTripleCode
  omega

/-- Every address in the actual symmetric partition support has compound-label sum `26`. -/
theorem cw112SymmetricBlockNatValue_legal
    (K : Type u) [CommRing K] (q : ℕ)
    (address : BlockAddress CW112SymmetricBlock)
    (haddress : address ∈ (cw112SymmetricPartitionedTensor K q).support) :
    cw112SymmetricBlockNatValue .X (address .X) +
        cw112SymmetricBlockNatValue .Y (address .Y) +
        cw112SymmetricBlockNatValue .Z (address .Z) = 26 := by
  have hcombinatorial : address ∈ cw112SymmetricSupport := by
    rwa [cw112SymmetricPartitionedTensor_support] at haddress
  let supported : CW112SymmetricSupport := ⟨address, hcombinatorial⟩
  let source := cw112SymmetricSupportEquiv.symm supported
  have hreconstruct : cw112SymmetricAddress source = address := by
    have h := congrArg Subtype.val
      (cw112SymmetricSupportEquiv.apply_symm_apply supported)
    exact h
  rw [← hreconstruct]
  exact cw112SymmetricBlockNatValue_address_sum source

/-- Cast the compound natural label into a sufficiently large prime field. -/
def cw112SymmetricBlockFieldValue (p : ℕ) : ∀ c, CW112SymmetricBlock c → ZMod p :=
  fun c block ↦ cw112SymmetricBlockNatValue c block

/-- Compound labels remain injective after casting into `ZMod p` when `p ≥ 27`. -/
theorem cw112SymmetricBlockFieldValue_injective
    {p : ℕ} [NeZero p] (hp : 27 ≤ p) (c : Leg) :
    Function.Injective (cw112SymmetricBlockFieldValue p c) := by
  intro left right h
  change (cw112SymmetricBlockNatValue c left : ZMod p) =
    (cw112SymmetricBlockNatValue c right : ZMod p) at h
  have hleft : cw112SymmetricBlockNatValue c left < p :=
    (cw112SymmetricBlockNatValue_lt c left).trans_le hp
  have hright : cw112SymmetricBlockNatValue c right < p :=
    (cw112SymmetricBlockNatValue_lt c right).trans_le hp
  have hval := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hleft, ZMod.val_natCast_of_lt hright] at hval
  exact cw112SymmetricBlockNatValue_injective c hval

/-- The symmetric 64-address support as one legal ordinary three-leg hashing support.

Unlike the historical two-leg presentation, zeroing is not built into this definition.  The
encoding only proves finite support geometry; the subsequent extraction theorem may compose it
with any suitable tensor transformation relation. -/
def cw112SymmetricPartitionHashEncoding
    (K : Type u) [CommRing K] (q p : ℕ) [Fact p.Prime] (hp : 27 ≤ p) :
    PartitionHashEncoding (R := ZMod p)
      (cw112SymmetricPartitionedTensor K q).support := by
  letI : NeZero p := ⟨by omega⟩
  refine
    { encode := cw112SymmetricBlockFieldValue p
      target := 26
      support_nonempty := ⟨
        (cw112SymmetricPartitionSupportEquiv K q
          ((cw112DiagonalFirstS, cw112DiagonalFirstS), cw112DiagonalFirstS)).1,
        (cw112SymmetricPartitionSupportEquiv K q
          ((cw112DiagonalFirstS, cw112DiagonalFirstS), cw112DiagonalFirstS)).2⟩
      encode_injective := cw112SymmetricBlockFieldValue_injective hp
      legal := ?_ }
  intro address haddress
  have hnat := cw112SymmetricBlockNatValue_legal K q address haddress
  change (cw112SymmetricBlockNatValue .X (address .X) : ZMod p) +
      (cw112SymmetricBlockNatValue .Y (address .Y) : ZMod p) +
      (cw112SymmetricBlockNatValue .Z (address .Z) : ZMod p) = (26 : ZMod p)
  have hcast := congrArg (fun n : ℕ ↦ (n : ZMod p)) hnat
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hcast

end AlgebraicComplexity.Examples
