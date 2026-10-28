import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.InvariantNeighborhood
import OAI.NumberTheory.ArithmeticGroups.Lattices.InverseHaarTranslations

/-! # Factor Haar Invariance -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.FactorHaarInvariance.Construction

noncomputable section

/-! Right Haar measure is invariant under left translations by a
compact subgroup. A finite positive invariant neighborhood forces the scale to one. -/

open scoped ENNReal
open _root_.MeasureTheory _root_.MeasureTheory.Measure Set

theorem measurePreserving_of_scalar_and_finite_invariant_set
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → X) (hf : Measurable f)
    (c : ℝ≥0∞) (hscale : μ.map f = c • μ)
    (D : Set X) (hD : MeasurableSet D) (hD₀ : μ D ≠ 0) (hDfin : μ D ≠ ⊤)
    (hpre : f ⁻¹' D = D) : MeasurePreserving f μ μ := by
  have hm : c * μ D = μ D := by
    rw [← smul_eq_mul, ← Measure.smul_apply, ← hscale, Measure.map_apply hf hD, hpre]
  have hc : c = 1 := (ENNReal.mul_eq_right hD₀ hDfin).mp hm
  exact ⟨hf, by rw [hscale, hc, one_smul]⟩

theorem inverseHaar_left_compact_subgroup_invariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] [InnerRegular μ]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (g : G) (hg : g ∈ K) :
    MeasurePreserving (g * ·) μ.inv μ.inv := by
  obtain ⟨D, hD, hD₁, hpre⟩ := InvariantNeighborhood.Construction.compact_subgroup_invariant_compact_neighborhood K hK
  exact measurePreserving_of_scalar_and_finite_invariant_set μ.inv (g * ·) (measurable_const_mul g)
    (modularCharacterFun g⁻¹ : ℝ≥0∞) (InverseHaarTranslations.Construction.inverseHaar_left_translation_scalar μ g)
    D hD.measurableSet (measure_pos_of_mem_nhds μ.inv hD₁).ne' hD.measure_lt_top.ne (hpre g hg)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.FactorHaarInvariance.Construction
