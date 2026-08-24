import AlgebraicComplexity.Tensor.Restriction

set_option linter.style.header false

/-!
# Finite rank witnesses for trilinear tensors

The predicate `HasRankAtMost r T` is witness-oriented: it stores a finite list of pure terms
summing to `T`. This is convenient for machine-generated rank certificates and does not require
choosing a minimum rank.
-/

namespace AlgebraicComplexity
namespace TriTensor

universe u

variable
    {K X Y Z X' Y' Z' : Type u}
    [CommSemiring K]
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [AddCommMonoid X'] [AddCommMonoid Y'] [AddCommMonoid Z']
    [Module K X] [Module K Y] [Module K Z]
    [Module K X'] [Module K Y'] [Module K Z']

/-- One rank-one summand of a trilinear tensor. -/
structure PureTerm (K X Y Z : Type u)
    [CommSemiring K]
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [Module K X] [Module K Y] [Module K Z] where
  x : X
  y : Y
  z : Z

namespace PureTerm

/-- Interpret a rank-one witness as a pure tensor. -/
def toTensor (p : PureTerm K X Y Z) : TriTensor K X Y Z :=
  pure p.x p.y p.z

/-- Apply coordinatewise linear maps to a rank-one witness. -/
def map (f : X →ₗ[K] X') (g : Y →ₗ[K] Y') (h : Z →ₗ[K] Z')
    (p : PureTerm K X Y Z) : PureTerm K X' Y' Z' :=
  ⟨f p.x, g p.y, h p.z⟩

@[simp]
theorem toTensor_map (f : X →ₗ[K] X') (g : Y →ₗ[K] Y') (h : Z →ₗ[K] Z')
    (p : PureTerm K X Y Z) :
    (map f g h p).toTensor = TriTensor.map3 f g h p.toTensor := by
  cases p
  simp [toTensor, map]

end PureTerm

/-- Sum the pure tensors represented by a list of rank-one witnesses. -/
def realize (terms : List (PureTerm K X Y Z)) : TriTensor K X Y Z :=
  (terms.map PureTerm.toTensor).sum

@[simp]
theorem realize_nil : realize ([] : List (PureTerm K X Y Z)) = 0 := by
  simp [realize]

@[simp]
theorem realize_cons (p : PureTerm K X Y Z) (terms : List (PureTerm K X Y Z)) :
    realize (p :: terms) = p.toTensor + realize terms := by
  simp [realize]

@[simp]
theorem realize_append (left right : List (PureTerm K X Y Z)) :
    realize (left ++ right) = realize left + realize right := by
  simp [realize]

/-- Realization commutes with coordinatewise linear maps. -/
theorem map3_realize
    (f : X →ₗ[K] X') (g : Y →ₗ[K] Y') (h : Z →ₗ[K] Z')
    (terms : List (PureTerm K X Y Z)) :
    TriTensor.map3 f g h (realize terms) =
      realize (terms.map (PureTerm.map f g h)) := by
  induction terms with
  | nil => simp
  | cons p terms ih => simp [ih]

/-- A concrete certificate that `T` is a sum of at most `r` pure tensors. -/
def HasRankAtMost (r : ℕ) (T : TriTensor K X Y Z) : Prop :=
  ∃ terms : List (PureTerm K X Y Z), terms.length ≤ r ∧ realize terms = T

namespace HasRankAtMost

/-- The zero tensor has rank at most zero. -/
theorem zero : HasRankAtMost (K := K) 0 (0 : TriTensor K X Y Z) := by
  refine ⟨([] : List (PureTerm K X Y Z)), by simp, ?_⟩
  rfl

/-- A pure tensor has rank at most one. -/
theorem pure (x : X) (y : Y) (z : Z) :
    HasRankAtMost (K := K) 1 (TriTensor.pure (K := K) x y z) := by
  let term : PureTerm K X Y Z := ⟨x, y, z⟩
  refine ⟨[term], by simp, ?_⟩
  simp [realize, term, PureTerm.toTensor]

/-- A rank bound remains true after weakening the numerical bound. -/
theorem mono {r s : ℕ} {T : TriTensor K X Y Z}
    (h : HasRankAtMost (K := K) r T) (hrs : r ≤ s) :
    HasRankAtMost (K := K) s T := by
  rcases h with ⟨terms, hlen, hsum⟩
  exact ⟨terms, hlen.trans hrs, hsum⟩

/-- Rank witnesses concatenate under addition. -/
theorem add {r s : ℕ} {T S : TriTensor K X Y Z}
    (hT : HasRankAtMost (K := K) r T) (hS : HasRankAtMost (K := K) s S) :
    HasRankAtMost (K := K) (r + s) (T + S) := by
  rcases hT with ⟨left, hleft, rfl⟩
  rcases hS with ⟨right, hright, rfl⟩
  refine ⟨left ++ right, ?_, by simp⟩
  simpa using Nat.add_le_add hleft hright

/-- Coordinatewise linear maps do not increase a concrete rank bound. -/
theorem map {r : ℕ} {T : TriTensor K X Y Z}
    (hT : HasRankAtMost (K := K) r T)
    (f : X →ₗ[K] X') (g : Y →ₗ[K] Y') (h : Z →ₗ[K] Z') :
    HasRankAtMost (K := K) r (TriTensor.map3 f g h T) := by
  rcases hT with ⟨terms, hlen, hsum⟩
  refine ⟨terms.map (PureTerm.map f g h), by simpa using hlen, ?_⟩
  calc
    realize (terms.map (PureTerm.map f g h)) =
        TriTensor.map3 f g h (realize terms) := (map3_realize f g h terms).symm
    _ = TriTensor.map3 f g h T := by rw [hsum]

/-- Exact tensor restriction cannot increase a concrete rank bound. -/
theorem of_restricts {r : ℕ} {T : TriTensor K X Y Z} {S : TriTensor K X' Y' Z'}
    (hTS : Restricts T S) (hT : HasRankAtMost (K := K) r T) :
    HasRankAtMost (K := K) r S := by
  rcases hTS with ⟨f, g, h, rfl⟩
  exact hT.map f g h

end HasRankAtMost
end TriTensor
end AlgebraicComplexity
