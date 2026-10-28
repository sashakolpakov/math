import OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeylFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylAnalysis

/-! # Real Reconstruction Haar -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealReconstructionHaar.Construction

noncomputable section

/-! Positive real Weyl reconstruction for arbitrary Haar normalizations. -/

open _root_.MeasureTheory
open scoped SchwartzMap ComplexConjugate

theorem realSchwartz_energy_pos {d : ℕ} (u : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) (hu : u ≠ 0) :
    0 < ∫ x : Local.FunctionsMetaplectic.Construction.Position ℝ d, ‖u x‖ ^ 2 := by
  have hex : ∃ x, u x ≠ 0 := by
    by_contra h
    apply hu
    ext x
    exact not_not.mp (fun hx => h ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := hex
  have hi : Integrable (fun x : Local.FunctionsMetaplectic.Construction.Position ℝ d => ‖u x‖ ^ 2) :=
    (u.memLp (p := 2) volume).integrable_norm_pow (by decide)
  exact integral_pos_of_integrable_nonneg_nonzero (u.continuous.norm.pow 2) hi
    (fun _ => sq_nonneg _) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

theorem realWeyl_reconstruction_haar {d : ℕ} (a : ℝ) (ha : a ≠ 0)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)) [μ.IsAddHaarMeasure]
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (u : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) (hu : u ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ f : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ, ∀ x,
      WeylSynthesisAdd.Construction.weylSynthesis (RealFourier.Construction.realCharacter a) ν (WeylAnalysis.Construction.weylAnalysis (RealFourier.Construction.realCharacter a) μ u f) u x = (r : ℂ) * f x := by
  let ρ := (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)).prod (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  let : ρ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure
    (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d)) (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  let : ρ.Regular := by
    let : SigmaCompactSpace (Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d) := inferInstance
    let : IsFiniteMeasureOnCompacts ρ := inferInstance
    let : IsLocallyFiniteMeasure ρ := inferInstance
    exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ρ
  let e := (RealWeylCoefficients.Construction.realPhasePairCoordinates d).toContinuousAddEquiv
  let ν' := ν.map e
  let : ν'.IsAddHaarMeasure := e.isAddHaarMeasure_map ν
  let b := Measure.addHaarScalarFactor ν' ρ
  have hb : 0 < b := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν' ρ
  have hν : ν' = b • ρ := Measure.isAddLeftInvariant_eq_smul_of_regular ν' ρ
  let c := Measure.addHaarScalarFactor μ (volume : Measure (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul_of_regular μ volume
  let U : ℝ := ∫ x : Local.FunctionsMetaplectic.Construction.Position ℝ d, ‖u x‖ ^ 2
  have hU : 0 < U := realSchwartz_energy_pos u hu
  have hUi : (∫ y : Local.FunctionsMetaplectic.Construction.Position ℝ d, conj (u y) * u y) = (U : ℂ) := by
    simp_rw [Complex.conj_mul', ← Complex.ofReal_pow]
    exact integral_complex_ofReal
  refine ⟨(b : ℝ) * (c : ℝ) * |a|⁻¹ ^ d * U, ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos hb hc) (pow_pos (inv_pos.mpr (abs_pos.mpr ha)) d)) hU
  · intro f x
    let T : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℂ := fun v =>
      conj (WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) μ u f v) * Local.FunctionsMetaplectic.Construction.heisenbergFunction (RealFourier.Construction.realCharacter a) v u x
    have htrans : (∫ v, T v ∂ν) = ∫ z, T (e.symm z) ∂ν' := by
      change _ = ∫ z, T (e.symm z) ∂ν.map e.toHomeomorph
      rw [e.toHomeomorph.isClosedEmbedding.integral_map]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        change T v = T (e.symm (e v))
        rw [e.symm_apply_apply]
    have hcoeff (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) :
        WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) μ u f v =
          (c : ℂ) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) volume u f v := by
      unfold WeylMatrixCoefficients.Construction.weylMatrixCoefficient
      rw [hμ, integral_smul_nnreal_measure]
      rfl
    have heq (z : Local.FunctionsMetaplectic.Construction.Position ℝ d × Local.FunctionsMetaplectic.Construction.Position ℝ d) : T (e.symm z) = (c : ℂ) *
        (conj (WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) volume u f (Sum.elim z.1 z.2)) *
          Local.FunctionsMetaplectic.Construction.heisenbergFunction (RealFourier.Construction.realCharacter a) (Sum.elim z.1 z.2) u x) := by
      change conj (WeylMatrixCoefficients.Construction.weylMatrixCoefficient (RealFourier.Construction.realCharacter a) μ u f (Sum.elim z.1 z.2)) * _ = _
      rw [hcoeff, map_mul]
      have hcconj : conj (c : ℂ) = (c : ℂ) := Complex.conj_ofReal (c : ℝ)
      rw [hcconj, mul_assoc]
      rfl
    change (∫ v, T v ∂ν) = _
    rw [htrans, hν, integral_smul_nnreal_measure]
    change (b : ℂ) * (∫ z, T (e.symm z) ∂ρ) = _
    simp_rw [heq]
    rw [integral_const_mul, RealWeylFourier.Construction.realWeyl_reconstruction_pair a ha u f x, hUi]
    push_cast
    ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealReconstructionHaar.Construction
