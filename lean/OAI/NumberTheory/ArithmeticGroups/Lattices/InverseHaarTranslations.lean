import OAI.NumberTheory.ArithmeticGroups.Lattices.FiniteDomainMeasureRigidity

/-! # Inverse Haar Translations -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InverseHaarTranslations.Construction

noncomputable section

/-! Inverse Haar measure is right invariant, and every left translate
is a scalar multiple. A finite fundamental domain forces those scalars
to equal one. -/

open scoped Classical ENNReal
open Set _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem map_left_inverse_measure
    {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H] [MeasurableInv H]
    (μ : Measure H) (g : H) :
    μ.inv.map (g * ·) = (μ.map (· * g⁻¹)).inv := by
  simp only [Measure.inv, Measure.map_map (measurable_const_mul g) measurable_inv,
    Measure.map_map measurable_inv (measurable_mul_const g⁻¹)]
  congr 1
  funext x
  simp only [Function.comp_apply, mul_inv_rev, inv_inv]

theorem inverseHaar_left_translation_scalar
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsHaarMeasure μ] [InnerRegular μ] (g : H) :
    μ.inv.map (g * ·) = (modularCharacterFun g⁻¹ : ℝ≥0∞) • μ.inv := by
  rw [map_left_inverse_measure, map_right_mul_eq_modularCharacterFun_smul]
  simp only [Measure.inv]
  rw [Measure.map_smul _ measurable_inv.aemeasurable]
  rfl

theorem inverseHaar_left_invariant_of_finite_fundamentalDomain
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [IsHaarMeasure μ] [InnerRegular μ] (hμ0 : μ.inv ≠ 0)
    (Γ : Subgroup H) [Countable Γ]
    (F : Set H) (hFmeas : MeasurableSet F) (hF : IsFundamentalDomain Γ.op F μ.inv)
    (hFfin : μ.inv F < ⊤) : IsMulLeftInvariant μ.inv := by
  constructor
  intro g
  exact (FiniteDomainMeasureRigidity.Construction.measurePreserving_of_scalar_and_finite_fundamentalDomain μ.inv hμ0 F hFmeas hF hFfin
    (g * ·) (measurable_const_mul g) (fun γ x => (mul_assoc g x γ.val.unop).symm)
    (modularCharacterFun g⁻¹ : ℝ≥0∞) (inverseHaar_left_translation_scalar μ g)).map_eq

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InverseHaarTranslations.Construction
