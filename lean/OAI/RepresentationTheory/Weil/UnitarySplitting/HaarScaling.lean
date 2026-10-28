import Mathlib

/-! # Haar Scaling -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.HaarScaling.Construction

noncomputable section

/-! Uniqueness and coordinate invariance of additive Haar scaling factors. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

theorem nnreal_smul_measure_injective
    {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] (x : X) :
    Function.Injective (fun r : ℝ≥0 => r • μ) := by
  obtain ⟨U, hx, hU, hfin⟩ := μ.exists_isOpen_measure_lt_top x
  have hpos : 0 < (μ U).toReal := ENNReal.toReal_pos (hU.measure_pos μ ⟨x, hx⟩).ne' hfin.ne
  intro r s hrs
  have hh := congrArg (fun ν : Measure X => (ν U).toReal) hrs
  change ((r : ℝ≥0∞) * μ U).toReal = ((s : ℝ≥0∞) * μ U).toReal at hh
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hh
  exact NNReal.coe_injective (mul_right_cancel₀ hpos.ne' hh)

variable {A B : Type} [AddGroup A] [AddGroup B]
variable [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]
variable [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
variable [LocallyCompactSpace A] [LocallyCompactSpace B]
variable [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B]

omit [T2Space A] in
theorem addHaarChar_eq_of_smul_map (μ : Measure A) [μ.IsAddHaarMeasure] [μ.Regular]
    (φ : A ≃ₜ+ A) (r : ℝ≥0) (hr : r • μ.map φ = μ) :
    r = addEquivAddHaarChar φ := by
  apply nnreal_smul_measure_injective (μ.map φ) (0 : A)
  exact hr.trans (addEquivAddHaarChar_smul_map μ φ).symm

omit [T2Space A] [T2Space B] in
theorem addHaarChar_intertwining (e : A ≃ₜ+ B) (φ : A ≃ₜ+ A) (ψ : B ≃ₜ+ B)
    (he : ∀ x, e (φ x) = ψ (e x)) : addEquivAddHaarChar φ = addEquivAddHaarChar ψ := by
  let μ : Measure A := Measure.addHaar
  let ν : Measure B := μ.map e
  let : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let : ν.Regular := Measure.Regular.map e.toHomeomorph
  have hmap : (μ.map φ).map e = ν.map ψ := by
    rw [Measure.map_map (show Measurable e from e.continuous.measurable)
      (show Measurable φ from φ.continuous.measurable)]
    change μ.map (e ∘ φ) = (μ.map e).map ψ
    rw [Measure.map_map (show Measurable ψ from ψ.continuous.measurable)
      (show Measurable e from e.continuous.measurable)]
    congr 1
    exact funext he
  apply addHaarChar_eq_of_smul_map ν ψ
  have hh := congrArg (Measure.map e) (addEquivAddHaarChar_smul_map μ φ)
  have hpush := Measure.map_smul (μ := μ.map φ) (f := (e : A → B))
    (addEquivAddHaarChar φ) e.continuous.measurable.aemeasurable
  rw [hpush, hmap] at hh
  exact hh

def continuousProdAddEquiv (φ : A ≃ₜ+ A) (ψ : B ≃ₜ+ B) : A × B ≃ₜ+ A × B where
  toAddEquiv := φ.toAddEquiv.prodCongr ψ.toAddEquiv
  continuous_toFun := φ.continuous.prodMap ψ.continuous
  continuous_invFun := φ.symm.continuous.prodMap ψ.symm.continuous

theorem addHaarChar_prod [SecondCountableTopology A] [SecondCountableTopology B]
    (φ : A ≃ₜ+ A) (ψ : B ≃ₜ+ B) :
    addEquivAddHaarChar (continuousProdAddEquiv φ ψ) = addEquivAddHaarChar φ * addEquivAddHaarChar ψ := by
  let μ : Measure A := Measure.addHaar
  let ν : Measure B := Measure.addHaar
  apply Eq.symm
  apply addHaarChar_eq_of_smul_map (μ.prod ν) (continuousProdAddEquiv φ ψ)
  have hm : (μ.prod ν).map (continuousProdAddEquiv φ ψ) = (μ.map φ).prod (ν.map ψ) :=
    (Measure.map_prod_map μ ν (show Measurable φ from φ.continuous.measurable)
      (show Measurable ψ from ψ.continuous.measurable)).symm
  rw [hm]
  calc
    _ = (addEquivAddHaarChar φ • μ.map φ).prod (addEquivAddHaarChar ψ • ν.map ψ) := by
      rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    _ = μ.prod ν := by rw [addEquivAddHaarChar_smul_map, addEquivAddHaarChar_smul_map]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.HaarScaling.Construction
