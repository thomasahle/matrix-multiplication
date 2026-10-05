import Mathlib.Data.ZMod.Basic

/-!
# Exact ternary encodings of three finite coordinates

Affine hashing needs injective field labels for compound block alphabets.  Three natural digits in
`{0,1,2}` can be packed as `x + 3y + 9z`; the result is below `27`, and equality of packed values
recovers every digit.  Casting this code to `ZMod p` stays injective whenever `27 ≤ p`.

This tiny module is independent of tensors and named constructions.  It is useful whenever a
three-factor product support must be represented in one sufficiently large prime field.
-/

namespace AlgebraicComplexity

/-- The three-digit base-three natural-number code. -/
def ternaryTripleCode (x y z : ℕ) : ℕ := x + 3 * y + 9 * z

/-- Three ternary digits encode to a natural number below `27`. -/
theorem ternaryTripleCode_lt
    {x y z : ℕ} (hx : x < 3) (hy : y < 3) (hz : z < 3) :
    ternaryTripleCode x y z < 27 := by
  unfold ternaryTripleCode
  omega

/-- Equality of codes for ternary digits implies coordinatewise equality.

Proof sketch: the units digit is determined modulo three; after removing it, the next digit is
again determined modulo three, and the remaining quotient is the final digit.  `omega` performs
this bounded Presburger calculation directly. -/
theorem ternaryTripleCode_injectiveOn
    {x y z x' y' z' : ℕ}
    (hx : x < 3) (hy : y < 3) (_hz : z < 3)
    (hx' : x' < 3) (hy' : y' < 3) (_hz' : z' < 3)
    (hcode : ternaryTripleCode x y z = ternaryTripleCode x' y' z') :
    x = x' ∧ y = y' ∧ z = z' := by
  unfold ternaryTripleCode at hcode
  omega

/-- Casting bounded ternary codes into `ZMod p` is injective once `p ≥ 27`.

Proof sketch: both codes are strictly below `p`, so their `ZMod` representatives have the original
natural values.  Equality in the field therefore gives equality of natural codes, after which the
bounded uniqueness theorem recovers all three digits. -/
theorem ternaryTripleCode_zmod_injectiveOn
    {p x y z x' y' z' : ℕ} [NeZero p]
    (hp : 27 ≤ p)
    (hx : x < 3) (hy : y < 3) (hz : z < 3)
    (hx' : x' < 3) (hy' : y' < 3) (hz' : z' < 3)
    (hcode : (ternaryTripleCode x y z : ZMod p) =
      (ternaryTripleCode x' y' z' : ZMod p)) :
    x = x' ∧ y = y' ∧ z = z' := by
  have hleft : ternaryTripleCode x y z < p :=
    (ternaryTripleCode_lt hx hy hz).trans_le hp
  have hright : ternaryTripleCode x' y' z' < p :=
    (ternaryTripleCode_lt hx' hy' hz').trans_le hp
  have hval := congrArg ZMod.val hcode
  rw [ZMod.val_natCast_of_lt hleft, ZMod.val_natCast_of_lt hright] at hval
  exact ternaryTripleCode_injectiveOn hx hy hz hx' hy' hz' hval

end AlgebraicComplexity
