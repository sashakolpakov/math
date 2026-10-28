import OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteCovolume

/-! # Compact Quotient Projection -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CompactQuotientProjection

noncomputable section

section

/-! Push quotient probability measures through surjective group homomorphisms,
including passage to the closure of the projected arithmetic subgroup. -/

open scoped Classical
open _root_.MeasureTheory OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure.Construction

variable {G L : Type*} [Group G] [Group L]

def quotientProjection (f : G →* L) (Γ : Subgroup G) (Δ : Subgroup L)
    (h : Γ.map f ≤ Δ) : G ⧸ Γ → L ⧸ Δ :=
  Quotient.map' f fun x y hxy => by
    apply QuotientGroup.leftRel_apply.mpr
    apply h
    have hmem := QuotientGroup.leftRel_apply.mp hxy
    simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem f hmem

theorem quotientProjection_smul (f : G →* L) (Γ : Subgroup G) (Δ : Subgroup L)
    (h : Γ.map f ≤ Δ) (g : G) (x : G ⧸ Γ) :
    quotientProjection f Γ Δ h (g • x) = f g • quotientProjection f Γ Δ h x := by
  obtain ⟨y, rfl⟩ := Quotient.exists_rep x
  change QuotientGroup.mk (f (g * y)) = QuotientGroup.mk (f g * f y)
  rw [map_mul]

variable [TopologicalSpace G] [TopologicalSpace L]

theorem continuous_quotientProjection (f : G →* L) (hf : Continuous f)
    (Γ : Subgroup G) (Δ : Subgroup L) (h : Γ.map f ≤ Δ) :
    Continuous (quotientProjection f Γ Δ h) := hf.quotient_map' _

/-- A finite, nonzero invariant quotient measure, normalized to total mass one. -/
def QuotientHasInvariantProbability (Γ : Subgroup G) : Prop :=
  letI : MeasurableSpace (G ⧸ Γ) := borel (G ⧸ Γ)
  ∃ μ : Measure (G ⧸ Γ), IsProbabilityMeasure μ ∧ SMulInvariantMeasure G (G ⧸ Γ) μ

theorem quotientProbability_of_surjective [IsTopologicalGroup L]
    (f : G →* L) (hf : Continuous f) (hsurj : Function.Surjective f)
    (Γ : Subgroup G) (Δ : Subgroup L) (h : Γ.map f ≤ Δ)
    (hΓ : QuotientHasInvariantProbability Γ) : QuotientHasInvariantProbability Δ := by
  let : MeasurableSpace (G ⧸ Γ) := borel (G ⧸ Γ)
  let : BorelSpace (G ⧸ Γ) := ⟨rfl⟩
  let : MeasurableSpace (L ⧸ Δ) := borel (L ⧸ Δ)
  let : BorelSpace (L ⧸ Δ) := ⟨rfl⟩
  obtain ⟨μ, hprob, hinv⟩ := hΓ
  let : IsProbabilityMeasure μ := hprob
  let : SMulInvariantMeasure G (G ⧸ Γ) μ := hinv
  have hm := (continuous_quotientProjection f hf Γ Δ h).measurable
  refine ⟨μ.map (quotientProjection f Γ Δ h),
    inferInstance, ?_⟩
  exact ArithmeticGroups.Lattices.QuotientMeasure.Construction.invariant_measure_map_of_surjective f hsurj _ hm
    (quotientProjection_smul f Γ Δ h) μ

/-- The local closure of a projected lattice inherits a quotient probability
measure. Discreteness of the projected subgroup is not required. -/
theorem projectedClosure_quotientProbability [IsTopologicalGroup L]
    (f : G →* L) (hf : Continuous f) (hsurj : Function.Surjective f)
    (Γ : Subgroup G) (hΓ : QuotientHasInvariantProbability Γ) :
    QuotientHasInvariantProbability (Γ.map f).topologicalClosure :=
  quotientProbability_of_surjective f hf hsurj Γ _
    (Γ.map f).le_topologicalClosure hΓ

theorem projectedClosure_finiteIndex [IsTopologicalGroup L] [SecondCountableTopology L]
    (f : G →* L) (hf : Continuous f) (hsurj : Function.Surjective f)
    (Γ : Subgroup G) (hΓ : QuotientHasInvariantProbability Γ)
    (hopen : IsOpen ((Γ.map f).topologicalClosure : Set L)) :
    (Γ.map f).topologicalClosure.FiniteIndex := by
  obtain ⟨μ, hprob, hinv⟩ := projectedClosure_quotientProbability f hf hsurj Γ hΓ
  exact FiniteCovolume.finiteIndex_of_open_invariant_probability _ hopen μ hprob hinv

end

/-! Continuous surjective homomorphisms preserve compactness of
homogeneous quotients under projection of the subgroup. -/

theorem quotientProjection_surjective {G L : Type*} [Group G] [Group L]
    (f : G →* L) (hf : Function.Surjective f) (Γ : Subgroup G) (Δ : Subgroup L)
    (h : Γ.map f ≤ Δ) : Function.Surjective (quotientProjection f Γ Δ h) := by
  intro z
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  obtain ⟨g, rfl⟩ := hf x
  exact ⟨QuotientGroup.mk g, rfl⟩

theorem compact_quotient_of_surjective {G L : Type*} [Group G] [Group L]
    [TopologicalSpace G] [TopologicalSpace L] (f : G →* L) (hf : Continuous f)
    (hs : Function.Surjective f) (Γ : Subgroup G) (Δ : Subgroup L) (h : Γ.map f ≤ Δ)
    [CompactSpace (G ⧸ Γ)] : CompactSpace (L ⧸ Δ) :=
  (quotientProjection_surjective f hs Γ Δ h).compactSpace (continuous_quotientProjection f hf Γ Δ h)

end

end OAI.NumberTheory.Quaternion.Arithmetic.CompactQuotientProjection
