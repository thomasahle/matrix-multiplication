/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareConstituents

/-!
# The exceptional `112` Coppersmith--Winograd square constituent

The coarse `112` constituent is not itself one rectangular matrix-multiplication tensor.  Its X
and Y spaces each contain two `q`-coordinate families, while its Z space contains two corner
coordinates and a `q × q` grid.  This file gives those coordinates names and identifies the
coarsened constituent with the four-family normal form displayed in the proof of the lemma on
journal pages 270--272 of Coppersmith--Winograd (1990).

The normal-form theorem is an exact constructive restriction.  Each of the four raw products in
the `112` fiber is expanded into pure terms, and the coordinate selector is checked on every pure
term.  The later C-tensor/type-counting argument can therefore work with `cw112Tensor` without
assuming that it represents the original constituent.

This file deliberately does not yet prove the asymptotic value estimate
`2^(2/3) * q^tau * (q^(3*tau) + 2)^(1/3)`.  That estimate uses even tensor powers, balanced word
types, hashing, and the C-tensor form of Schönhage's inequality, and belongs after this exact
coordinate interface.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The two orientations of a degree-one block, or equivalently the two corner coordinates in
the degree-two Z block. -/
inductive CW112Side
  | first
  | second
  deriving DecidableEq

/-- The side type has exactly its two named orientations. -/
instance : Fintype CW112Side where
  elems := {.first, .second}
  complete side := by cases side <;> simp

/-- Readable coordinate sets for the three legs of the exceptional constituent.

The X and Y coordinates are a side together with an index in `Fin q`.  The Z coordinates are
either one of two corners or a pair in the `q × q` grid. -/
abbrev CW112Index (q : ℕ) : Leg → Type
  | .X => CW112Side × Fin q
  | .Y => CW112Side × Fin q
  | .Z => CW112Side ⊕ (Fin q × Fin q)

/-- Equality of named `112` coordinates is decidable on every leg. -/
instance (q : ℕ) (c : Leg) : DecidableEq (CW112Index q c) := by
  cases c <;> simp only [CW112Index] <;> infer_instance

/-- Every named `112` coordinate set is finite. -/
instance (q : ℕ) (c : Leg) : Fintype (CW112Index q c) := by
  cases c <;> simp only [CW112Index] <;> infer_instance

/-- Standard coordinate vector spaces for the exceptional normal form. -/
abbrev CW112Space (K : Type u) (q : ℕ) (c : Leg) := CW112Index q c → K

/-- A standard basis vector in one leg of `CW112Space`. -/
noncomputable def cw112Basis {K : Type u} [Zero K] [One K]
    (q : ℕ) (c : Leg) (a : CW112Index q c) : CW112Space K q c :=
  Pi.single a 1

/-- Embed the named `112` coordinates into the generic sigma coordinates of a coarsened square
block.  `first` means `(middle,zero)` on X and Y and `(zero,last)` on Z. -/
def cw112CoordinateIndex (q : ℕ) : ∀ c,
    CW112Index q c → CWSquareBlockCoordinate q c (cwSquare112 c)
  | .X, (.first, i) => ⟨⟨(.middle, .zero), by decide⟩, (i, ())⟩
  | .X, (.second, i) => ⟨⟨(.zero, .middle), by decide⟩, ((), i)⟩
  | .Y, (.first, i) => ⟨⟨(.middle, .zero), by decide⟩, (i, ())⟩
  | .Y, (.second, i) => ⟨⟨(.zero, .middle), by decide⟩, ((), i)⟩
  | .Z, .inl .first => ⟨⟨(.zero, .last), by decide⟩, ((), ())⟩
  | .Z, .inl .second => ⟨⟨(.last, .zero), by decide⟩, ((), ())⟩
  | .Z, .inr (i, k) => ⟨⟨(.middle, .middle), by decide⟩, (i, k)⟩

/-- Leg maps from the coarsened `112` block to its readable coordinate normal form. -/
noncomputable def cw112Map (K : Type u) [CommRing K] (q : ℕ) : ∀ c,
    CWSquareBlockSpace K q c (cwSquare112 c) →ₗ[K] CW112Space K q c :=
  fun c ↦ LinearMap.funLeft K K (cw112CoordinateIndex q c) ∘ₗ
    (cwSquareBlockCoordinateEquiv K q c (cwSquare112 c)).toLinearMap

/-- One pure term in the readable `112` coordinates. -/
noncomputable def cw112Pure (K : Type u) [CommRing K] (q : ℕ)
    (x : CW112Index q .X) (y : CW112Index q .Y) (z : CW112Index q .Z) :
    Tensor3 K (CW112Space K q) :=
  pure (K := K) (ofLegs (cw112Basis q .X x) (cw112Basis q .Y y)
    (cw112Basis q .Z z))

/-- The diagonal family on the first orientation. -/
noncomputable def cw112DiagonalFirst (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (CW112Space K q) :=
  ∑ i : Fin q, cw112Pure K q (.first, i) (.first, i) (.inl .first)

/-- The diagonal family on the second orientation. -/
noncomputable def cw112DiagonalSecond (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (CW112Space K q) :=
  ∑ i : Fin q, cw112Pure K q (.second, i) (.second, i) (.inl .second)

/-- The first cross family, coupling first-oriented X variables to second-oriented Y variables. -/
noncomputable def cw112CrossFirst (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (CW112Space K q) :=
  ∑ i : Fin q, ∑ k : Fin q,
    cw112Pure K q (.first, i) (.second, k) (.inr (i, k))

/-- The second cross family, coupling second-oriented X variables to first-oriented Y variables. -/
noncomputable def cw112CrossSecond (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (CW112Space K q) :=
  ∑ i : Fin q, ∑ k : Fin q,
    cw112Pure K q (.second, k) (.first, i) (.inr (i, k))

/-- The four-family normal form of the exceptional constituent. -/
noncomputable def cw112Tensor (K : Type u) [CommRing K] (q : ℕ) :
    Tensor3 K (CW112Space K q) :=
  cw112DiagonalFirst K q + cw112DiagonalSecond K q +
    cw112CrossFirst K q + cw112CrossSecond K q

/-- One raw term from the `002 ⊗ 110` source branch. -/
noncomputable def cw112Raw002110Term (K : Type u) [CommRing K] (q : ℕ) (i : Fin q) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw002 cw110 c)) :=
  external
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .last ())))
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .zero ())))

/-- One raw term from the `110 ⊗ 002` source branch. -/
noncomputable def cw112Raw110002Term (K : Type u) [CommRing K] (q : ℕ) (i : Fin q) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw110 cw002 c)) :=
  external
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .zero ())))
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .last ())))

/-- One raw term from the `011 ⊗ 101` source branch. -/
noncomputable def cw112Raw011101Term (K : Type u) [CommRing K]
    (q : ℕ) (i k : Fin q) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw011 cw101 c)) :=
  external
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .middle i)))
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .middle k)
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .middle k)))

/-- One raw term from the `101 ⊗ 011` source branch. -/
noncomputable def cw112Raw101011Term (K : Type u) [CommRing K]
    (q : ℕ) (i k : Fin q) :
    Tensor3 K (fun c ↦ CWSquareRawBlockSpace K q c
      (cwSquareRawAddress cw101 cw011 c)) :=
  external
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .middle i)))
    (pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .middle k)
      (cwBlockBasis K q .middle k)))

section CoordinateCertificate

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- A defining term of `002 ⊗ 110` maps to the corresponding second-oriented diagonal term.

Proof sketch: the X and Y variables lie in the `(zero,middle)` fiber, while Z lies in the
`(last,zero)` corner fiber.  Evaluating `cw112Map` therefore selects side `second` on all three
legs, and the tensor-product coordinate equivalence sends the two standard basis vectors to their
paired standard basis vector. -/
theorem map_cw112Map_002_110_pure (i : Fin q) :
    map (cw112Map K q)
        (map
          (coarsenedBlockIncludeAt
            (K := K) (V := CWSquareRawBlockSpace K q)
            cwSquareDegreeMap (cwSquareRawAddress cw002 cw110) cwSquare112 (by decide))
          (external
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .last ())))
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .middle i)
              (cwBlockBasis K q .middle i)
              (cwBlockBasis K q .zero ()))))) =
      cw112Pure K q (.second, i) (.second, i) (.inl .second) := by
  simp only [external_pure, Tensor.map_pure, cw112Pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨side, k⟩
      cases side with
      | first =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change (0 : K) =
            (Pi.single (.second, i) (1 : K) : CW112Space K q .X) (.first, k)
          simp
      | second =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change coordinateTensorEquiv (K := K)
              ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
                (Pi.single i (1 : K) : Fin q → K)) ((), k) =
            (Pi.single (.second, i) (1 : K) : CW112Space K q .X) (.second, k)
          rw [coordinateTensorEquiv_single_tmul_single]
          simp [Pi.single_apply]
  | Y =>
      ext a
      rcases a with ⟨side, k⟩
      cases side with
      | first =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change (0 : K) =
            (Pi.single (.second, i) (1 : K) : CW112Space K q .Y) (.first, k)
          simp
      | second =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change coordinateTensorEquiv (K := K)
              ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
                (Pi.single i (1 : K) : Fin q → K)) ((), k) =
            (Pi.single (.second, i) (1 : K) : CW112Space K q .Y) (.second, k)
          rw [coordinateTensorEquiv_single_tmul_single]
          simp [Pi.single_apply]
  | Z =>
      ext a
      rcases a with side | ik
      · cases side with
        | first =>
            simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
              cw112CoordinateIndex]
            change (0 : K) =
              (Pi.single (.inl .second) (1 : K) : CW112Space K q .Z) (.inl .first)
            simp
        | second =>
            simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
              cw112CoordinateIndex]
            change coordinateTensorEquiv (K := K)
                ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
                  (Pi.single () (1 : K) : Unit → K)) ((), ()) =
              (Pi.single (.inl .second) (1 : K) : CW112Space K q .Z) (.inl .second)
            rw [coordinateTensorEquiv_single_tmul_single]
            simp
      · rcases ik with ⟨j, k⟩
        simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
          cw112CoordinateIndex]
        change (0 : K) =
          (Pi.single (.inl .second) (1 : K) : CW112Space K q .Z) (.inr (j, k))
        simp

/-- A defining term of `110 ⊗ 002` maps to the corresponding first-oriented diagonal term.

This is the factor-reversed companion of `map_cw112Map_002_110_pure`: X and Y now lie in the
`(middle,zero)` fiber, and Z lies in the `(zero,last)` corner fiber. -/
theorem map_cw112Map_110_002_pure (i : Fin q) :
    map (cw112Map K q)
        (map
          (coarsenedBlockIncludeAt
            (K := K) (V := CWSquareRawBlockSpace K q)
            cwSquareDegreeMap (cwSquareRawAddress cw110 cw002) cwSquare112 (by decide))
          (external
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .middle i)
              (cwBlockBasis K q .middle i)
              (cwBlockBasis K q .zero ())))
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .last ()))))) =
      cw112Pure K q (.first, i) (.first, i) (.inl .first) := by
  simp only [external_pure, Tensor.map_pure, cw112Pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨side, k⟩
      cases side with
      | first =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change coordinateTensorEquiv (K := K)
              ((Pi.single i (1 : K) : Fin q → K) ⊗ₜ[K]
                (Pi.single () (1 : K) : Unit → K)) (k, ()) =
            (Pi.single (.first, i) (1 : K) : CW112Space K q .X) (.first, k)
          rw [coordinateTensorEquiv_single_tmul_single]
          simp [Pi.single_apply]
      | second =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change (0 : K) =
            (Pi.single (.first, i) (1 : K) : CW112Space K q .X) (.second, k)
          simp
  | Y =>
      ext a
      rcases a with ⟨side, k⟩
      cases side with
      | first =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change coordinateTensorEquiv (K := K)
              ((Pi.single i (1 : K) : Fin q → K) ⊗ₜ[K]
                (Pi.single () (1 : K) : Unit → K)) (k, ()) =
            (Pi.single (.first, i) (1 : K) : CW112Space K q .Y) (.first, k)
          rw [coordinateTensorEquiv_single_tmul_single]
          simp [Pi.single_apply]
      | second =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change (0 : K) =
            (Pi.single (.first, i) (1 : K) : CW112Space K q .Y) (.second, k)
          simp
  | Z =>
      ext a
      rcases a with side | jk
      · cases side with
        | first =>
            simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
              cw112CoordinateIndex]
            change coordinateTensorEquiv (K := K)
                ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
                  (Pi.single () (1 : K) : Unit → K)) ((), ()) =
              (Pi.single (.inl .first) (1 : K) : CW112Space K q .Z) (.inl .first)
            rw [coordinateTensorEquiv_single_tmul_single]
            simp
        | second =>
            simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
              cw112CoordinateIndex]
            change (0 : K) =
              (Pi.single (.inl .first) (1 : K) : CW112Space K q .Z) (.inl .second)
            simp
      · rcases jk with ⟨j, k⟩
        simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
          cw112CoordinateIndex]
        change (0 : K) =
          (Pi.single (.inl .first) (1 : K) : CW112Space K q .Z) (.inr (j, k))
        simp

/-- A defining term of `011 ⊗ 101` maps to the second cross family.

The left index appears on Y and first in the Z-grid pair; the right index appears on X and
second in the Z-grid pair.  Thus the image has X side `second`, Y side `first`, and Z coordinate
`(i,k)`. -/
theorem map_cw112Map_011_101_pure (i k : Fin q) :
    map (cw112Map K q)
        (map
          (coarsenedBlockIncludeAt
            (K := K) (V := CWSquareRawBlockSpace K q)
            cwSquareDegreeMap (cwSquareRawAddress cw011 cw101) cwSquare112 (by decide))
          (external
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .middle i)
              (cwBlockBasis K q .middle i)))
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .middle k)
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .middle k))))) =
      cw112Pure K q (.second, k) (.first, i) (.inr (i, k)) := by
  simp only [external_pure, Tensor.map_pure, cw112Pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨side, j⟩
      cases side with
      | first =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change (0 : K) =
            (Pi.single (.second, k) (1 : K) : CW112Space K q .X) (.first, j)
          simp
      | second =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change coordinateTensorEquiv (K := K)
              ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
                (Pi.single k (1 : K) : Fin q → K)) ((), j) =
            (Pi.single (.second, k) (1 : K) : CW112Space K q .X) (.second, j)
          rw [coordinateTensorEquiv_single_tmul_single]
          simp [Pi.single_apply]
  | Y =>
      ext a
      rcases a with ⟨side, j⟩
      cases side with
      | first =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change coordinateTensorEquiv (K := K)
              ((Pi.single i (1 : K) : Fin q → K) ⊗ₜ[K]
                (Pi.single () (1 : K) : Unit → K)) (j, ()) =
            (Pi.single (.first, i) (1 : K) : CW112Space K q .Y) (.first, j)
          rw [coordinateTensorEquiv_single_tmul_single]
          simp [Pi.single_apply]
      | second =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change (0 : K) =
            (Pi.single (.first, i) (1 : K) : CW112Space K q .Y) (.second, j)
          simp
  | Z =>
      ext a
      rcases a with side | jl
      · cases side with
        | first =>
            simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
              cw112CoordinateIndex]
            change (0 : K) =
              (Pi.single (.inr (i, k)) (1 : K) : CW112Space K q .Z) (.inl .first)
            simp
        | second =>
            simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
              cw112CoordinateIndex]
            change (0 : K) =
              (Pi.single (.inr (i, k)) (1 : K) : CW112Space K q .Z) (.inl .second)
            simp
      · rcases jl with ⟨j, l⟩
        simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
          cw112CoordinateIndex]
        change coordinateTensorEquiv (K := K)
            ((Pi.single i (1 : K) : Fin q → K) ⊗ₜ[K]
              (Pi.single k (1 : K) : Fin q → K)) (j, l) =
          (Pi.single (.inr (i, k)) (1 : K) : CW112Space K q .Z) (.inr (j, l))
        rw [coordinateTensorEquiv_single_tmul_single]
        simp [Pi.single_apply]

/-- A defining term of `101 ⊗ 011` maps to the first cross family.

Here the left index appears on X and first in the Z-grid pair, while the right index appears on Y
and second in that pair.  This is the X/Y-side reversal of `map_cw112Map_011_101_pure`. -/
theorem map_cw112Map_101_011_pure (i k : Fin q) :
    map (cw112Map K q)
        (map
          (coarsenedBlockIncludeAt
            (K := K) (V := CWSquareRawBlockSpace K q)
            cwSquareDegreeMap (cwSquareRawAddress cw101 cw011) cwSquare112 (by decide))
          (external
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .middle i)
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .middle i)))
            (pure (K := K) (ofLegs
              (cwBlockBasis K q .zero ())
              (cwBlockBasis K q .middle k)
              (cwBlockBasis K q .middle k))))) =
      cw112Pure K q (.first, i) (.second, k) (.inr (i, k)) := by
  simp only [external_pure, Tensor.map_pure, cw112Pure]
  congr 1
  funext c
  cases c with
  | X =>
      ext a
      rcases a with ⟨side, j⟩
      cases side with
      | first =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change coordinateTensorEquiv (K := K)
              ((Pi.single i (1 : K) : Fin q → K) ⊗ₜ[K]
                (Pi.single () (1 : K) : Unit → K)) (j, ()) =
            (Pi.single (.first, i) (1 : K) : CW112Space K q .X) (.first, j)
          rw [coordinateTensorEquiv_single_tmul_single]
          simp [Pi.single_apply]
      | second =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change (0 : K) =
            (Pi.single (.first, i) (1 : K) : CW112Space K q .X) (.second, j)
          simp
  | Y =>
      ext a
      rcases a with ⟨side, j⟩
      cases side with
      | first =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change (0 : K) =
            (Pi.single (.second, k) (1 : K) : CW112Space K q .Y) (.first, j)
          simp
      | second =>
          simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
            cw112CoordinateIndex]
          change coordinateTensorEquiv (K := K)
              ((Pi.single () (1 : K) : Unit → K) ⊗ₜ[K]
                (Pi.single k (1 : K) : Fin q → K)) ((), j) =
            (Pi.single (.second, k) (1 : K) : CW112Space K q .Y) (.second, j)
          rw [coordinateTensorEquiv_single_tmul_single]
          simp [Pi.single_apply]
  | Z =>
      ext a
      rcases a with side | jl
      · cases side with
        | first =>
            simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
              cw112CoordinateIndex]
            change (0 : K) =
              (Pi.single (.inr (i, k)) (1 : K) : CW112Space K q .Z) (.inl .first)
            simp
        | second =>
            simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
              cw112CoordinateIndex]
            change (0 : K) =
              (Pi.single (.inr (i, k)) (1 : K) : CW112Space K q .Z) (.inl .second)
            simp
      · rcases jl with ⟨j, l⟩
        simp only [cw112Map, LinearMap.comp_apply, LinearMap.funLeft_apply,
          cw112CoordinateIndex]
        change coordinateTensorEquiv (K := K)
            ((Pi.single i (1 : K) : Fin q → K) ⊗ₜ[K]
              (Pi.single k (1 : K) : Fin q → K)) (j, l) =
          (Pi.single (.inr (i, k)) (1 : K) : CW112Space K q .Z) (.inr (j, l))
        rw [coordinateTensorEquiv_single_tmul_single]
        simp [Pi.single_apply]

/-! ## From raw branches to the full constituent -/

/-- The raw `002 ⊗ 110` constituent is the sum of its `q` displayed pure terms. -/
theorem cwSquareRawConstituent_002_110 :
    ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress cw002 cw110) =
      ∑ i : Fin q, cw112Raw002110Term K q i := by
  rw [cwSquareRawConstituent]
  change external
      (cwConstituentOfBlocks K q .zero .zero .last)
      (cwConstituentOfBlocks K q .middle .middle .zero) = _
  simp only [cwConstituentOfBlocks, cw112Raw002110Term]
  exact external_fintypeSum_right _ _

/-- The raw `110 ⊗ 002` constituent is the sum of its `q` displayed pure terms. -/
theorem cwSquareRawConstituent_110_002 :
    ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress cw110 cw002) =
      ∑ i : Fin q, cw112Raw110002Term K q i := by
  rw [cwSquareRawConstituent]
  change external
      (cwConstituentOfBlocks K q .middle .middle .zero)
      (cwConstituentOfBlocks K q .zero .zero .last) = _
  simp only [cwConstituentOfBlocks, cw112Raw110002Term]
  exact external_fintypeSum_left _ _

/-- The raw `011 ⊗ 101` constituent is the double sum of its `q²` displayed pure terms. -/
theorem cwSquareRawConstituent_011_101 :
    ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress cw011 cw101) =
      ∑ i : Fin q, ∑ k : Fin q, cw112Raw011101Term K q i k := by
  rw [cwSquareRawConstituent]
  change external
      (cwConstituentOfBlocks K q .zero .middle .middle)
      (cwConstituentOfBlocks K q .middle .zero .middle) = _
  simp only [cwConstituentOfBlocks, cw112Raw011101Term]
  exact external_sum_sum _ _

/-- The raw `101 ⊗ 011` constituent is the double sum of its `q²` displayed pure terms. -/
theorem cwSquareRawConstituent_101_011 :
    ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress cw101 cw011) =
      ∑ i : Fin q, ∑ k : Fin q, cw112Raw101011Term K q i k := by
  rw [cwSquareRawConstituent]
  change external
      (cwConstituentOfBlocks K q .middle .zero .middle)
      (cwConstituentOfBlocks K q .zero .middle .middle) = _
  simp only [cwConstituentOfBlocks, cw112Raw101011Term]
  exact external_sum_sum _ _

/-- The transported `002 ⊗ 110` branch maps to the second diagonal family. -/
theorem map_cw112Map_002_110_branch :
    map (cw112Map K q)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw002 cw110)) =
      cw112DiagonalSecond K q := by
  rw [coarsenedTerm_eq_map_of_eq
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap cwSquare112
    (cwSquareRawAddress cw002 cw110) (by decide)]
  rw [cwSquareRawConstituent_002_110]
  simp only [cw112DiagonalSecond, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [cw112Raw002110Term] using map_cw112Map_002_110_pure K q i

/-- The transported `110 ⊗ 002` branch maps to the first diagonal family. -/
theorem map_cw112Map_110_002_branch :
    map (cw112Map K q)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw110 cw002)) =
      cw112DiagonalFirst K q := by
  rw [coarsenedTerm_eq_map_of_eq
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap cwSquare112
    (cwSquareRawAddress cw110 cw002) (by decide)]
  rw [cwSquareRawConstituent_110_002]
  simp only [cw112DiagonalFirst, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [cw112Raw110002Term] using map_cw112Map_110_002_pure K q i

/-- The transported `011 ⊗ 101` branch maps to the second cross family. -/
theorem map_cw112Map_011_101_branch :
    map (cw112Map K q)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw011 cw101)) =
      cw112CrossSecond K q := by
  rw [coarsenedTerm_eq_map_of_eq
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap cwSquare112
    (cwSquareRawAddress cw011 cw101) (by decide)]
  rw [cwSquareRawConstituent_011_101]
  simp only [cw112CrossSecond, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simpa only [cw112Raw011101Term] using map_cw112Map_011_101_pure K q i k

/-- The transported `101 ⊗ 011` branch maps to the first cross family. -/
theorem map_cw112Map_101_011_branch :
    map (cw112Map K q)
        (coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw101 cw011)) =
      cw112CrossFirst K q := by
  rw [coarsenedTerm_eq_map_of_eq
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap cwSquare112
    (cwSquareRawAddress cw101 cw011) (by decide)]
  rw [cwSquareRawConstituent_101_011]
  simp only [cw112CrossFirst, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simpa only [cw112Raw101011Term] using map_cw112Map_101_011_pure K q i k

/-- The explicit coordinate maps identify the exceptional coarse constituent with the readable
four-family tensor `cw112Tensor`.

Proof sketch: expand the coarsened constituent into its four source branches, apply the four
branch mapping theorems, and reorder the resulting sum into the normal-form convention. -/
theorem map_cw112Map_constituent :
    map (cw112Map K q)
        ((cwSquarePartitionedTensor K q).constituent cwSquare112) =
      cw112Tensor K q := by
  rw [cwSquareConstituent_112, map_add, map_add, map_add,
    map_cw112Map_002_110_branch, map_cw112Map_110_002_branch,
    map_cw112Map_011_101_branch, map_cw112Map_101_011_branch]
  unfold cw112Tensor
  abel

/-- Exact paper-facing interface for the exceptional class: the coarsened `112` constituent
restricts to the four-family normal form used by the C-tensor value argument.

The restriction witness is the explicit coordinate selector `cw112Map`; there is no assumed
constituent-value proposition in this theorem. -/
theorem cwSquareConstituent_112_restricts :
    Restricts
      ((cwSquarePartitionedTensor K q).constituent cwSquare112)
      (cw112Tensor K q) :=
  ⟨cw112Map K q, map_cw112Map_constituent K q⟩

end CoordinateCertificate

end AlgebraicComplexity.Examples
