import AlgebraicComplexity.Combinatorics.MarkedLegwiseHashingExtraction

/-!
# Aggregate marked hashing for heterogeneous finite families

Hashing several typed constituents independently takes a minimum over the three collision
branches in every factor before their exponents are added.  Recursive laser certificates instead
form the three directional totals first and take one minimum afterwards.

This file supplies the finite combinatorial operation needed for the latter.  A function of
legal triples is concatenated over the sigma type of all factor positions.  Sharing one aggregate
leg is then exactly sharing that leg in every factor, so the aggregate leg-fiber cardinality is
the product of the factor leg-fiber cardinalities.  One application of marked affine hashing
therefore pays

`max_c prod_e (factorFiber e c)`

rather than `prod_e max_c (factorFiber e c)`.

The theorem is tensor-independent.  A semantic client still has to identify its externally
assembled constituent family with these aggregate legal triples and zero the selected aggregate
support to the corresponding tensor direct sum.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R]
variable {E : Type v} [Fintype E] [DecidableEq E]
variable {ι : E → Type w} [∀ e, Fintype (ι e)]
variable {target : R}

/-- Concatenate a heterogeneous finite family of legal triples into one legal triple. -/
def aggregate (triple : ∀ e, LegalTriple R (ι e) target) :
    LegalTriple R (Sigma ι) target where
  xIndex position := (triple position.1).xIndex position.2
  yIndex position := (triple position.1).yIndex position.2
  zIndex position := (triple position.1).zIndex position.2
  legal position := (triple position.1).legal position.2

@[simp] theorem aggregate_xIndex_apply
    (triple : ∀ e, LegalTriple R (ι e) target) (e : E) (i : ι e) :
    (aggregate triple).xIndex ⟨e, i⟩ = (triple e).xIndex i := rfl

@[simp] theorem aggregate_yIndex_apply
    (triple : ∀ e, LegalTriple R (ι e) target) (e : E) (i : ι e) :
    (aggregate triple).yIndex ⟨e, i⟩ = (triple e).yIndex i := rfl

@[simp] theorem aggregate_zIndex_apply
    (triple : ∀ e, LegalTriple R (ι e) target) (e : E) (i : ι e) :
    (aggregate triple).zIndex ⟨e, i⟩ = (triple e).zIndex i := rfl

@[simp] theorem aggregate_legIndex_apply
    (triple : ∀ e, LegalTriple R (ι e) target) (c : Tensor.Leg)
    (e : E) (i : ι e) :
    (aggregate triple).legIndex c ⟨e, i⟩ = (triple e).legIndex c i := by
  cases c <;> rfl

theorem aggregate_injective :
    Function.Injective
      (aggregate : (∀ e, LegalTriple R (ι e) target) →
        LegalTriple R (Sigma ι) target) := by
  intro left right h
  funext e
  apply LegalTriple.ext
  · funext i
    exact congrFun (congrArg LegalTriple.xIndex h) ⟨e, i⟩
  · funext i
    exact congrFun (congrArg LegalTriple.yIndex h) ⟨e, i⟩
  · funext i
    exact congrFun (congrArg LegalTriple.zIndex h) ⟨e, i⟩

/-- Cartesian product of factor target families, represented as aggregate legal triples. -/
noncomputable def aggregateTargets
    (targets : ∀ e, Finset (LegalTriple R (ι e) target)) :
    Finset (LegalTriple R (Sigma ι) target) :=
  by
    classical
    exact (Fintype.piFinset targets).image aggregate

theorem mem_aggregateTargets
    (targets : ∀ e, Finset (LegalTriple R (ι e) target))
    (triple : LegalTriple R (Sigma ι) target) :
    triple ∈ aggregateTargets targets ↔
      ∃ factors : ∀ e, LegalTriple R (ι e) target,
        (∀ e, factors e ∈ targets e) ∧ aggregate factors = triple := by
  classical
  simp only [aggregateTargets, Finset.mem_image, Fintype.mem_piFinset]

@[simp] theorem card_aggregateTargets
    (targets : ∀ e, Finset (LegalTriple R (ι e) target)) :
    (aggregateTargets targets).card = ∏ e, (targets e).card := by
  classical
  rw [aggregateTargets, Finset.card_image_of_injective _ aggregate_injective,
    Fintype.card_piFinset]

theorem aggregateTargets_mono
    {left right : ∀ e, Finset (LegalTriple R (ι e) target)}
    (h : ∀ e, left e ⊆ right e) :
    aggregateTargets left ⊆ aggregateTargets right := by
  classical
  intro triple htriple
  obtain ⟨factors, hfactors, rfl⟩ :=
    (mem_aggregateTargets left triple).mp htriple
  exact (mem_aggregateTargets right (aggregate factors)).mpr
    ⟨factors, fun e ↦ h e (hfactors e), rfl⟩

/-- Fixing one aggregate leg is the Cartesian product of fixing that leg in every factor. -/
theorem aggregate_legFiber_eq
    (targets : ∀ e, Finset (LegalTriple R (ι e) target))
    (triple : ∀ e, LegalTriple R (ι e) target) (c : Tensor.Leg) :
    legFiber (aggregateTargets targets) (aggregate triple) c =
      aggregateTargets (fun e ↦ legFiber (targets e) (triple e) c) := by
  classical
  ext other
  constructor
  · intro hother
    obtain ⟨haggregate, hleg⟩ :=
      (mem_legFiber (aggregateTargets targets) (aggregate triple) other c).mp hother
    obtain ⟨factors, hfactors, rfl⟩ :=
      (mem_aggregateTargets targets other).mp haggregate
    apply (mem_aggregateTargets
      (fun e ↦ legFiber (targets e) (triple e) c) (aggregate factors)).mpr
    refine ⟨factors, ?_, rfl⟩
    intro e
    apply (mem_legFiber (targets e) (triple e) (factors e) c).mpr
    refine ⟨hfactors e, ?_⟩
    funext i
    simpa only [aggregate_legIndex_apply] using congrFun hleg ⟨e, i⟩
  · intro hother
    obtain ⟨factors, hfactors, rfl⟩ :=
      (mem_aggregateTargets
        (fun e ↦ legFiber (targets e) (triple e) c)
        other).mp hother
    apply (mem_legFiber (aggregateTargets targets)
      (aggregate triple) (aggregate factors) c).mpr
    constructor
    · apply (mem_aggregateTargets targets (aggregate factors)).mpr
      exact ⟨factors, fun e ↦
        (mem_legFiber (targets e) (triple e) (factors e) c).mp (hfactors e) |>.1,
        rfl⟩
    · funext position
      cases position with
      | mk e i =>
        rw [aggregate_legIndex_apply, aggregate_legIndex_apply]
        exact congrFun
          ((mem_legFiber (targets e) (triple e) (factors e) c).mp (hfactors e)).2 i

/-- Exact product formula for an aggregate directional fiber. -/
@[simp] theorem card_aggregate_legFiber
    (targets : ∀ e, Finset (LegalTriple R (ι e) target))
    (triple : ∀ e, LegalTriple R (ι e) target) (c : Tensor.Leg) :
    (legFiber (aggregateTargets targets) (aggregate triple) c).card =
      ∏ e, (legFiber (targets e) (triple e) c).card := by
  rw [aggregate_legFiber_eq, card_aggregateTargets]

/-- The aggregate collision-proxy count is bounded by the sum of the three directional fiber
products.  This is the branch-before-maximum count required by heterogeneous laser objectives. -/
theorem card_aggregate_legwiseCompetitorYIndices_le_sum_products
    (targets : ∀ e, Finset (LegalTriple R (ι e) target))
    (triple : ∀ e, LegalTriple R (ι e) target) :
    (legwiseCompetitorYIndices (aggregateTargets targets)
      (aggregate triple)).card ≤
      ∑ c : Tensor.Leg, ∏ e,
        (legFiber (targets e) (triple e) c).card := by
  simpa only [card_aggregate_legFiber] using
    card_legwiseCompetitorYIndices_le_sum_legFibers
      (aggregateTargets targets) (aggregate triple)

/-- Max-normalized form of the aggregate competitor bound. -/
theorem card_aggregate_legwiseCompetitorYIndices_le_three_mul
    (targets : ∀ e, Finset (LegalTriple R (ι e) target))
    (triple : ∀ e, LegalTriple R (ι e) target) (d : ℕ)
    (hfiber : ∀ c : Tensor.Leg,
      (∏ e, (legFiber (targets e) (triple e) c).card) ≤ d) :
    (legwiseCompetitorYIndices (aggregateTargets targets)
      (aggregate triple)).card ≤ 3 * d := by
  apply (card_aggregate_legwiseCompetitorYIndices_le_sum_products
    targets triple).trans
  rw [show (Finset.univ : Finset Tensor.Leg) = {.X, .Y, .Z} by decide]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_false, not_false_eq_true, Finset.sum_singleton]
  have hX := hfiber .X
  have hY := hfiber .Y
  have hZ := hfiber .Z
  omega

/-- Per-factor fiber bounds imply the branch-first aggregate field budget.

This is the certificate-facing form: each recursive node supplies three local bounds, while the
single aggregate hash multiplies them within a direction and sums only after those products have
been formed. -/
theorem aggregate_quarter_of_factorFiberBounds
    [Fintype R]
    (ambient marked : ∀ e, Finset (LegalTriple R (ι e) target))
    (bound : E → Tensor.Leg → ℕ)
    (hfiber : ∀ e (triple : LegalTriple R (ι e) target),
      triple ∈ marked e → ∀ c,
        (legFiber (ambient e) triple c).card ≤ bound e c)
    (hfield : 4 * (∑ c : Tensor.Leg, ∏ e, bound e c) ≤ Fintype.card R) :
    ∀ (factors : ∀ e, LegalTriple R (ι e) target),
      (∀ e, factors e ∈ marked e) →
      4 * (∑ c : Tensor.Leg, ∏ e,
        (legFiber (ambient e) (factors e) c).card) ≤ Fintype.card R := by
  intro factors hfactors
  apply (Nat.mul_le_mul_left 4 ?_).trans hfield
  exact Finset.sum_le_sum fun c _ ↦
    Finset.prod_le_prod' fun e _ ↦ hfiber e (factors e) (hfactors e) c

/-- One marked affine hash on a heterogeneous Cartesian product.

The field budget is checked against the three products of factor leg-fiber sizes.  In
particular, no factorwise maximum is taken. -/
theorem exists_seed_many_aggregateMarkedLegwiseIsolatedTargets
    [Fintype R] [NeZero (2 : R)]
    (ambient marked : ∀ e, Finset (LegalTriple R (ι e) target))
    (hmarked : ∀ e, marked e ⊆ ambient e)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ (factors : ∀ e, LegalTriple R (ι e) target),
      (∀ e, factors e ∈ marked e) →
      4 * (∑ c : Tensor.Leg, ∏ e,
        (legFiber (ambient e) (factors e) c).card) ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Sigma ι),
      3 * (∏ e, (marked e).card) * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (markedLegwiseIsolatedTargets
              (aggregateTargets ambient) (aggregateTargets marked) B seed).card ∧
        markedLegwiseIsolatedTargets
            (aggregateTargets ambient) (aggregateTargets marked) B seed ⊆
          filteredTargets (aggregateTargets ambient) B seed ∧
        ∀ leg, Set.InjOn
          (fun triple : LegalTriple R (Sigma ι) target ↦ triple.legIndex leg)
          (markedLegwiseIsolatedTargets
            (aggregateTargets ambient) (aggregateTargets marked) B seed : Set _) := by
  have hsubset : aggregateTargets marked ⊆ aggregateTargets ambient :=
    aggregateTargets_mono hmarked
  obtain ⟨seed, hcount, hfiltered, hinjective⟩ :=
    exists_seed_many_markedLegwiseIsolatedTargets
      (aggregateTargets ambient) (aggregateTargets marked) hsubset B hB (by
        intro triple htriple
        obtain ⟨factors, hfactors, rfl⟩ :=
          (mem_aggregateTargets marked triple).mp htriple
        exact (Nat.mul_le_mul_left 4
          (card_aggregate_legwiseCompetitorYIndices_le_sum_products
            ambient factors)).trans (hquarter factors hfactors))
  refine ⟨seed, ?_, hfiltered, hinjective⟩
  simpa only [card_aggregateTargets] using hcount

/-- Convenient field-budget corollary using one common upper bound for the three directional
fiber products. -/
theorem exists_seed_many_aggregateMarkedLegwiseIsolatedTargets_of_max
    [Fintype R] [NeZero (2 : R)]
    (ambient marked : ∀ e, Finset (LegalTriple R (ι e) target))
    (hmarked : ∀ e, marked e ⊆ ambient e)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (d : ℕ)
    (hfiber : ∀ (factors : ∀ e, LegalTriple R (ι e) target),
      (∀ e, factors e ∈ marked e) →
      ∀ c : Tensor.Leg,
        (∏ e, (legFiber (ambient e) (factors e) c).card) ≤ d)
    (hfield : 12 * d ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Sigma ι),
      3 * (∏ e, (marked e).card) * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (markedLegwiseIsolatedTargets
              (aggregateTargets ambient) (aggregateTargets marked) B seed).card ∧
        markedLegwiseIsolatedTargets
            (aggregateTargets ambient) (aggregateTargets marked) B seed ⊆
          filteredTargets (aggregateTargets ambient) B seed ∧
        ∀ leg, Set.InjOn
          (fun triple : LegalTriple R (Sigma ι) target ↦ triple.legIndex leg)
          (markedLegwiseIsolatedTargets
            (aggregateTargets ambient) (aggregateTargets marked) B seed : Set _) := by
  apply exists_seed_many_aggregateMarkedLegwiseIsolatedTargets
    ambient marked hmarked B hB
  intro factors hfactors
  have hX := hfiber factors hfactors .X
  have hY := hfiber factors hfactors .Y
  have hZ := hfiber factors hfactors .Z
  rw [show (Finset.univ : Finset Tensor.Leg) = {.X, .Y, .Z} by decide]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_false, not_false_eq_true, Finset.sum_singleton]
  omega

end ProgressionHash.LegalTriple

end AlgebraicComplexity
