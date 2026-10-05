/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PowerCoherence
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Positive powers of external tensor products

This file proves the structural identity

`(T ⊐ S)^(n+1) ≅ T^(n+1) ⊐ S^(n+1)`.

It exposes both the successor-shaped theorem `power_external_positive` and the certificate-facing
wrapper `power_external_of_pos`, whose exponent is arbitrary but accompanied by `0 < n`.  Only
positive powers are needed by finite typed-leaf and tensor-value certificates.  Keeping these
theorems here avoids importing asymptotic rank and the separate tensor-unit calculus merely to
move parentheses and interchange factors.  The all-exponents version, whose zero case needs the
unit object, remains `Tensor.Isomorphic.power_external` in `Tensor/AsymptoticRankCalculus.lean`.

The proof is basis-free and valid over every commutative semiring.  Its private helper is the
first-power transport; the middle-four interchange it builds on is
`Tensor.Isomorphic.external_interchange` of `Tensor/Product.lean`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

namespace Isomorphic

/-- The first canonical tensor power is isomorphic to the original tensor. -/
private theorem powerOneIso (T : Tensor3 K V) :
    Isomorphic (Tensor.power T 1) T := by
  rw [power_one_eq_powerOne]
  exact (Isomorphic.powerOneTransport T).symm

/-- Positive canonical powers distribute over factorwise external products.

In human terms, `(T ⊐ S)^(n+1)` differs from `T^(n+1) ⊐ S^(n+1)` only by canonical
reassociation and permutation of the tensor-product factors on each leg.

Proof sketch: the first-power case is the canonical `powerOne` transport.  At a successor,
split off the final copy of `T ⊐ S`, apply the induction hypothesis, use middle-four
interchange, and concatenate the two power blocks on each side. -/
theorem power_external_positive (T : Tensor3 K V) (S : Tensor3 K W) (n : ℕ) :
    Isomorphic (Tensor.power (Tensor.external T S) (n + 1))
      (Tensor.external (Tensor.power T (n + 1)) (Tensor.power S (n + 1))) := by
  induction n with
  | zero =>
      exact (powerOneIso (Tensor.external T S)).trans
        ((powerOneIso T).external (powerOneIso S)).symm
  | succ n ih =>
      refine ((isomorphic_external_power (Tensor.external T S) (n + 1) 1).symm.trans ?_)
      refine (ih.external (powerOneIso (Tensor.external T S))).trans ?_
      refine (external_interchange (Tensor.power T (n + 1))
        (Tensor.power S (n + 1)) T S).trans ?_
      exact (((Isomorphic.refl (Tensor.power T (n + 1))).external
          (powerOneIso T).symm).trans
            (isomorphic_external_power T (n + 1) 1)).external
        (((Isomorphic.refl (Tensor.power S (n + 1))).external
          (powerOneIso S).symm).trans
            (isomorphic_external_power S (n + 1) 1))

/-- Positive canonical powers distribute over external products, with positivity supplied as a
hypothesis rather than by a successor-shaped exponent.

This is the convenient form for certificates, whose power is stored as an arbitrary natural
number together with a proof that it is nonzero.

Proof sketch: positivity writes `n` as `m + 1`; apply `power_external_positive` at `m`. -/
theorem power_external_of_pos (T : Tensor3 K V) (S : Tensor3 K W)
    {n : ℕ} (hn : 0 < n) :
    Isomorphic (Tensor.power (Tensor.external T S) n)
      (Tensor.external (Tensor.power T n) (Tensor.power S n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact power_external_positive T S m

/-- Positive canonical powers commute with an arbitrary permutation of the three tensor legs.

This unbundled form works for module families in arbitrary universes.  It complements the
`LegModuleFamily`-based theorem used by positive-word extraction, while avoiding a universe
restriction in clients that only need canonical powers.

Proof sketch: split a successor power into its preceding positive power and its final copy,
apply the induction hypothesis to both factors, commute the leg permutation across their
external product, and concatenate the power blocks again. -/
theorem power_permute_positive_unbundled
    (T : Tensor3 K V) (n : ℕ) (e : Orientation) :
    Isomorphic (Tensor.power (Tensor.permute e T) (n + 1))
      (Tensor.permute e (Tensor.power T (n + 1))) := by
  induction n with
  | zero =>
      exact (powerOneIso (Tensor.permute e T)).trans
        ((powerOneIso T).permute_legs e).symm
  | succ n ih =>
      have hOne :
          Isomorphic (Tensor.power (Tensor.permute e T) 1)
            (Tensor.permute e (Tensor.power T 1)) :=
        (powerOneIso (Tensor.permute e T)).trans
          ((powerOneIso T).permute_legs e).symm
      have hsplit :
          Isomorphic (Tensor.power (Tensor.permute e T) ((n + 1) + 1))
            (Tensor.external
              (Tensor.power (Tensor.permute e T) (n + 1))
              (Tensor.power (Tensor.permute e T) 1)) :=
        (isomorphic_external_power (Tensor.permute e T) (n + 1) 1).symm
      have hparts :
          Isomorphic
            (Tensor.external
              (Tensor.power (Tensor.permute e T) (n + 1))
              (Tensor.power (Tensor.permute e T) 1))
            (Tensor.external
              (Tensor.permute e (Tensor.power T (n + 1)))
              (Tensor.permute e (Tensor.power T 1))) :=
        ih.external hOne
      have hcommute :
          Isomorphic
            (Tensor.external
              (Tensor.permute e (Tensor.power T (n + 1)))
              (Tensor.permute e (Tensor.power T 1)))
            (Tensor.permute e
              (Tensor.external (Tensor.power T (n + 1)) (Tensor.power T 1))) :=
        Isomorphic.of_eq
          (Tensor.permute_external e (Tensor.power T (n + 1)) (Tensor.power T 1)).symm
      have hjoin :
          Isomorphic
            (Tensor.permute e
              (Tensor.external (Tensor.power T (n + 1)) (Tensor.power T 1)))
            (Tensor.permute e (Tensor.power T ((n + 1) + 1))) :=
        (isomorphic_external_power T (n + 1) 1).permute_legs e
      exact hsplit.trans (hparts.trans (hcommute.trans hjoin))

end Isomorphic

end AlgebraicComplexity.Tensor
