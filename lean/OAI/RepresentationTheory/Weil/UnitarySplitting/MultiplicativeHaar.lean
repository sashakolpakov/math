import OAI.RepresentationTheory.Weil.UnitarySplitting.ModulusMeasure
import OAI.RepresentationTheory.Weil.UnitarySplitting.DensityPushforward

/-! # Multiplicative Haar -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.MultiplicativeHaar.Construction

noncomputable section

section

/-! Additive Haar measure on the nonzero field elements and its normalization
to a multiplicatively invariant measure. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

variable {F : Type} [NormedField F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]

omit [LocallyCompactSpace F] in
theorem unitsVal_measurableEmbedding : MeasurableEmbedding ((↑) : Fˣ → F) :=
  IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding

def unitsAdditiveMeasure (μ : Measure F) : Measure Fˣ := μ.comap ((↑) : Fˣ → F)

omit [LocallyCompactSpace F] in
theorem unitsAdditiveMeasure_apply (μ : Measure F) {S : Set Fˣ} (hS : MeasurableSet S) :
    unitsAdditiveMeasure μ S = μ (((↑) : Fˣ → F) '' S) :=
  Measure.comap_apply _ Units.val_injective
    (fun _ => unitsVal_measurableEmbedding.measurableSet_image.mpr) μ hS

theorem unitsAdditiveMeasure_scaled (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] (a : Fˣ) :
    FieldModulus.Construction.fieldModulus F a • (unitsAdditiveMeasure μ).map (fun x => a * x) = unitsAdditiveMeasure μ := by
  ext S hS
  rw [Measure.coe_nnreal_smul_apply, Measure.map_apply (measurable_const_mul a) hS,
    unitsAdditiveMeasure_apply μ ((measurable_const_mul a) hS), unitsAdditiveMeasure_apply μ hS]
  have heq : ((↑) : Fˣ → F) '' ((fun x => a * x) ⁻¹' S) =
      (FieldModulus.Construction.fieldDilation a) ⁻¹' (((↑) : Fˣ → F) '' S) := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨a * u, hu, rfl⟩
    · rintro ⟨u, hu, hy⟩
      refine ⟨a⁻¹ * u, ?_, ?_⟩
      · change a * (a⁻¹ * u) ∈ S
        simpa using hu
      · change (↑a⁻¹ : F) * (u : F) = y
        change (u : F) = (a : F) * y at hy
        rw [hy, ← mul_assoc, Units.inv_mul, one_mul]
  rw [heq]
  exact addEquivAddHaarChar_smul_preimage μ (FieldModulus.Construction.fieldDilation a)

def fieldMultiplicativeMeasure (μ : Measure F) : Measure Fˣ :=
  (unitsAdditiveMeasure μ).withDensity (fun a => (((FieldModulus.Construction.fieldModulus F a)⁻¹ : ℝ≥0) : ℝ≥0∞))

theorem fieldMultiplicativeMeasure_invariant (hF : ¬ DiscreteTopology F)
    (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] :
    (fieldMultiplicativeMeasure μ).IsMulLeftInvariant :=
  DensityPushforward.Construction.character_weight_invariant (unitsAdditiveMeasure μ) (FieldModulus.Construction.fieldModulus F)
    (ModulusMeasure.Construction.fieldModulus_measurable hF) FieldModulus.Construction.fieldModulus_pos (unitsAdditiveMeasure_scaled μ)

end

/-! Dividing additive Haar measure by its scaling character gives an actual
multiplicative Haar measure on the nonzero field elements. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

variable {F : Type} [NormedField F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]

omit [LocallyCompactSpace F] in
theorem unitsAdditiveMeasure_openPos (μ : Measure F) [μ.IsAddHaarMeasure] :
    (unitsAdditiveMeasure μ).IsOpenPosMeasure := by
  constructor
  intro U hU hne
  rw [unitsAdditiveMeasure_apply μ hU.measurableSet]
  exact (IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ hU).measure_ne_zero μ (hne.image _)

theorem fieldMultiplicativeMeasure_openPos (hF : ¬ DiscreteTopology F)
    (μ : Measure F) [μ.IsAddHaarMeasure] : (fieldMultiplicativeMeasure μ).IsOpenPosMeasure := by
  let ν := unitsAdditiveMeasure μ
  let : ν.IsOpenPosMeasure := unitsAdditiveMeasure_openPos μ
  let w : Fˣ → ℝ≥0∞ := fun a => (((FieldModulus.Construction.fieldModulus F a)⁻¹ : ℝ≥0) : ℝ≥0∞)
  have hw : Measurable w := measurable_coe_nnreal_ennreal.comp (ModulusMeasure.Construction.fieldModulus_measurable hF).inv
  have hwne : ∀ᵐ a ∂ν, w a ≠ 0 := Filter.Eventually.of_forall fun a => by
    dsimp only [w]
    exact_mod_cast inv_ne_zero (FieldModulus.Construction.fieldModulus_pos a).ne'
  have hac : ν ≪ ν.withDensity w := withDensity_absolutelyContinuous' hw.aemeasurable hwne
  constructor
  intro U hU hne hzero
  exact hU.measure_ne_zero ν hne (hac hzero)

theorem fieldMultiplicativeMeasure_isHaar (hF : ¬ DiscreteTopology F)
    (μ : Measure F) [μ.IsAddHaarMeasure] [μ.Regular] : (fieldMultiplicativeMeasure μ).IsHaarMeasure := by
  refine
    { toIsMulLeftInvariant := fieldMultiplicativeMeasure_invariant hF μ
      toIsOpenPosMeasure := fieldMultiplicativeMeasure_openPos hF μ
      lt_top_of_isCompact := ?_ }
  intro K hK
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne Units.continuous_val.norm.continuousOn
    have hb (b : Fˣ) (hb : b ∈ K) :
        (((FieldModulus.Construction.fieldModulus F b)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ (((FieldModulus.Construction.fieldModulus F a)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
      have hnorm : ‖(a : F)‖ ≤ ‖(b : F)‖ := hmin hb
      have hh := (inv_le_inv₀ (FieldModulus.Construction.fieldModulus_pos b) (FieldModulus.Construction.fieldModulus_pos a)).mpr
        (ModulusMeasure.Construction.fieldModulus_mono_norm hF a b hnorm)
      exact_mod_cast hh
    have hfin : unitsAdditiveMeasure μ K < ∞ := by
      rw [unitsAdditiveMeasure_apply μ hK.isClosed.measurableSet]
      exact (hK.image Units.continuous_val).measure_lt_top
    rw [fieldMultiplicativeMeasure, withDensity_apply _ hK.isClosed.measurableSet]
    calc
      _ ≤ ∫⁻ _ in K, (((FieldModulus.Construction.fieldModulus F a)⁻¹ : ℝ≥0) : ℝ≥0∞) ∂ unitsAdditiveMeasure μ :=
        setLIntegral_mono measurable_const hb
      _ = (((FieldModulus.Construction.fieldModulus F a)⁻¹ : ℝ≥0) : ℝ≥0∞) * unitsAdditiveMeasure μ K := by simp
      _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_ne_top.lt_top hfin
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
    exact ENNReal.zero_lt_top

theorem fieldMultiplicativeMeasure_withDensity_modulus (hF : ¬ DiscreteTopology F)
    (μ : Measure F) :
    (fieldMultiplicativeMeasure μ).withDensity (fun a => (FieldModulus.Construction.fieldModulus F a : ℝ≥0∞)) =
      unitsAdditiveMeasure μ := by
  have hw : Measurable (fun a : Fˣ => (((FieldModulus.Construction.fieldModulus F a)⁻¹ : ℝ≥0) : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (ModulusMeasure.Construction.fieldModulus_measurable hF).inv
  have hδ : Measurable (fun a : Fˣ => (FieldModulus.Construction.fieldModulus F a : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (ModulusMeasure.Construction.fieldModulus_measurable hF)
  rw [fieldMultiplicativeMeasure, ← withDensity_mul _ hw hδ]
  have heq : (fun a : Fˣ => (((FieldModulus.Construction.fieldModulus F a)⁻¹ : ℝ≥0) : ℝ≥0∞)) *
      (fun a : Fˣ => (FieldModulus.Construction.fieldModulus F a : ℝ≥0∞)) = 1 := by
    funext a
    change (((FieldModulus.Construction.fieldModulus F a)⁻¹ : ℝ≥0) : ℝ≥0∞) * (FieldModulus.Construction.fieldModulus F a : ℝ≥0∞) = 1
    rw [← ENNReal.coe_mul, inv_mul_cancel₀ (FieldModulus.Construction.fieldModulus_pos a).ne', ENNReal.coe_one]
  rw [heq, withDensity_one]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.MultiplicativeHaar.Construction
