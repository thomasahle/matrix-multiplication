/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogFormDefs

/-!
# Definition-only signed-log forms for dyadic entropy

This module contains the executable form constructors without their real-analysis correctness
proofs.  Generated checkers that only normalize exact forms can therefore avoid loading entropy
semantics and field tactics.

These are the unchanged constructors from the former `DyadicEntropyForm` monolith, separated as
part of a definition-preserving refactor of the existing certificate API, not a new paper result.

This module carries no claim of its own.  The homogeneous Shannon entropies it represents exactly
are the ones evaluated by the recursive Coppersmith--Winograd constituent analysis of
[alman2025more], `papers/sources/2404.16349/constituent.tex:113-147`, and by the dual certificate
of the Total-Weight manuscript, `better_bound/paper.tex`, `sec:dual` (lines 2274-2307).

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*.
-/

set_option autoImplicit false

namespace MatrixMultiplication.DyadicEntropyForm

open MatrixMultiplication.SignedDyadicLogForm

/-- Exact signed-log form for one Shannon summand at denominator `2^bits`. -/
def entropyTermForm (bits numerator : Nat) : Form :=
  if numerator = 0 then Form.zero
  else
    { constantNumerator := numerator * bits
      terms := [⟨numerator, -(numerator : Int)⟩] }

/-- Exact form for the sum of the Shannon summands of a serialized row. -/
def entropyForm (bits : Nat) (numerators : List Nat) : Form :=
  Form.sum (numerators.map (entropyTermForm bits))

/-- Exact form for homogeneous entropy.  This works for normalized rows, subprobability rows,
and the pooled mass rows occurring in compatibility penalties. -/
def weightedEntropyForm (bits : Nat) (numerators : List Nat) : Form :=
  Form.sub (entropyForm bits numerators) (entropyTermForm bits numerators.sum)

/-- Raise the represented denominator by `extra` bits without changing the real value. -/
def rescale (extra : Nat) (form : Form) : Form :=
  Form.scaleNat (2 ^ extra) form

end MatrixMultiplication.DyadicEntropyForm
