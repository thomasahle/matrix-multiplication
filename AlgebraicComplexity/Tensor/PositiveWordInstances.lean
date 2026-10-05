/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PositiveWordDefs
import Mathlib.Data.Fintype.Prod

/-!
# Standard instances for recursively represented nonempty words

This module equips `PositiveWord I n` with the recursive `Fintype`, `Nonempty`, and
`DecidableEq` instances needed by partitioned tensor powers.  It deliberately does not import the
equivalence with `Fin (n + 1) → I`; clients that need only finite recursive labels therefore avoid
the substantially larger finite-tuple import cone.
-/

namespace AlgebraicComplexity.Tensor

universe w

noncomputable instance positiveWordFintype {I : Type w} [Fintype I] :
    (n : Nat) → Fintype (PositiveWord I n)
  | Nat.zero => by simpa only [PositiveWord] using (inferInstanceAs (Fintype I))
  | Nat.succ n => by
      letI : Fintype (PositiveWord I n) := positiveWordFintype (I := I) n
      simpa only [PositiveWord] using
        (inferInstanceAs (Fintype (PositiveWord I n × I)))

/-- Positive words over a nonempty alphabet are nonempty. -/
instance positiveWordNonempty {I : Type w} [Nonempty I] :
    (n : Nat) → Nonempty (PositiveWord I n)
  | Nat.zero => inferInstanceAs (Nonempty I)
  | Nat.succ n => by
      letI : Nonempty (PositiveWord I n) := positiveWordNonempty (I := I) n
      simpa only [PositiveWord] using
        (inferInstanceAs (Nonempty (PositiveWord I n × I)))

/-- Decidable equality on nonempty recursive words. -/
instance positiveWordDecidableEq {I : Type w} [DecidableEq I] :
    (n : Nat) → DecidableEq (PositiveWord I n)
  | Nat.zero => inferInstanceAs (DecidableEq I)
  | Nat.succ n => by
      letI : DecidableEq (PositiveWord I n) := positiveWordDecidableEq (I := I) n
      simpa only [PositiveWord] using
        (inferInstanceAs (DecidableEq (PositiveWord I n × I)))

end AlgebraicComplexity.Tensor
