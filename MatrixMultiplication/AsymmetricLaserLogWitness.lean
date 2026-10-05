/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.RationalDyadicLog

/-!
# Finite logarithm witnesses for the shared asymmetric-laser certificate

The directed reconstruction in `better_bound/paper.tex:2496-2512,3537-3546` reduces entropy
expressions to signed rational sums of positive integer logarithms. This is the arithmetic
primitive for the entropy bounds in [duan2023faster], `global_value.tex:286-309`.

`LogAtom` uses exactly the five fields of the shared FW schema. Its validity predicate contains
only natural and rational comparisons. Soundness composes the committed rational cast bridge
with `FastDyadicLog`; it does not identify those endpoints with the different canonical
`IntegerEntropyDual` definitions. The geometric tail is conservative at every finite term count,
including zero. No compiler oracle, floating-point logarithm or optimizer is assumed.

This numerical adapter stays in the downstream certificate layer because its existing providers
live there. The semantic asymmetric-hashing modules do not import it.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.AsymmetricLaserData

/-- An exact positive-integer logarithm enclosure with an explicitly chosen reduction scale. -/
structure LogAtom where
  argument : Nat
  scale : Nat
  terms : Nat
  lower : ℚ
  upper : ℚ

/-- Check the supplied endpoints against the existing rational atanh enclosures.
The optional upper mantissa bound and a positive term count are not required for soundness. -/
def LogAtom.Valid (atom : LogAtom) : Prop :=
  0 < atom.argument ∧ 2 ^ atom.scale ≤ atom.argument ∧
    atom.lower ≤ MatrixMultiplication.RationalDyadicLog.numeratorLogLower
      atom.argument atom.scale atom.terms ∧
    MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
      atom.argument atom.scale atom.terms ≤ atom.upper

/-- The checked lower rational endpoint lies below the actual base-two logarithm. -/
theorem LogAtom.lower_le (atom : LogAtom) (h : atom.Valid) :
    (atom.lower : ℝ) ≤ Real.log (atom.argument : ℝ) / Real.log 2 :=
  (MatrixMultiplication.RationalDyadicLog.cast_le_fastLower h.2.2.1).trans
    (MatrixMultiplication.FastDyadicLog.numeratorLogLower_le h.2.1)

/-- The actual base-two logarithm lies below the checked upper rational endpoint. -/
theorem LogAtom.le_upper (atom : LogAtom) (h : atom.Valid) :
    Real.log (atom.argument : ℝ) / Real.log 2 ≤ (atom.upper : ℝ) :=
  (MatrixMultiplication.FastDyadicLog.le_numeratorLogUpper h.2.1).trans
    (MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast h.2.2.2)

end AlgebraicComplexity.AsymmetricLaserData
