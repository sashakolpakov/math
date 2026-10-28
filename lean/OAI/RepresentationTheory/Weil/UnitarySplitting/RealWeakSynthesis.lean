import OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeakGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakWeylSynthesis

/-! # Real Weak Synthesis -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeakSynthesis.Construction

noncomputable section

/-! Absolute convergence permits real Schwartz Weyl synthesis in weak Gaussian pairings. -/

open _root_.MeasureTheory
open scoped SchwartzMap ComplexConjugate

def correlationShiftCoordinates (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (V × V) ≃L[ℝ] (V × V) where
  toFun x := (x.1, -x.1 + x.2)
  invFun x := (x.1, x.1 + x.2)
  left_inv x := by simp only [add_neg_cancel_left]
  right_inv x := by simp only [neg_add_cancel_left]
  map_add' x y := by
    apply Prod.ext
    · rfl
    · change -(x.1 + y.1) + (x.2 + y.2) = (-x.1 + x.2) + (-y.1 + y.2)
      abel
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · change -(a • x.1) + a • x.2 = a • (-x.1 + x.2)
      rw [smul_add, smul_neg]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {d : ℕ} (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t))
variable (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]

include hn in
theorem realWeakWeylSynthesis_integrable
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℝ) (hq : Continuous q)
    (a : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ) (f u : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    Integrable (fun p : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d =>
      ψ (q p.2) * (conj (a p.1) * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d)
        f.val (HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu p.1 u).val p.2)) (ν.prod ν) := by
  let : (ν.prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure ν ν
  obtain ⟨C, hC⟩ := RealWeylCoefficients.Construction.exists_real_weyl_coefficient_schwartz ψ hc hu hn (Weak.Construction.referencePositionMeasure ℝ d) f u
  let K := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (correlationShiftCoordinates (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d))
    (SchwartzTensor.Construction.schwartzTensor (SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap a) C)
  have hKi : Integrable K (ν.prod ν) := K.integrable
  let k : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℂ := fun p =>
    ψ (q p.2) * (conj (a p.1) * (ψ (Oscillator.Construction.standardSymplecticPairing d (-p.1) p.2 / 2) * C (-p.1 + p.2)))
  have hkc : Continuous k := by unfold k Oscillator.Construction.standardSymplecticPairing; fun_prop
  have hki : Integrable k (ν.prod ν) := by
    apply hKi.norm.mono' hkc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      change ‖ψ (q p.2) * (conj (a p.1) * (ψ (Oscillator.Construction.standardSymplecticPairing d (-p.1) p.2 / 2) * C (-p.1 + p.2)))‖ ≤
        ‖conj (a p.1) * C (-p.1 + p.2)‖
      simp only [norm_mul, hu, one_mul, le_refl]
  convert hki using 1
  funext p
  rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_output_shift RealFourierUnitary.Construction.real_nondiscrete ψ hc hu]
  change _ = ψ (q p.2) * (conj (a p.1) * (ψ (Oscillator.Construction.standardSymplecticPairing d (-p.1) p.2 / 2) * C (-p.1 + p.2)))
  rw [hC]

include hn in
theorem realWeakWeylGaussian_synthesized_output
    (q : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℝ) (hq : Continuous q)
    (a : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ)
    (f u h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) (hh : h.val = WeylSynthesisAdd.Construction.weylSynthesis ψ ν a u.val) :
    WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν q f.val h.val =
      ∫ v, conj (a v) * WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν q
        f.val (HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu v u).val ∂ν := by
  have hki := realWeakWeylSynthesis_integrable ψ hc hu hn ν q hq a f u
  calc
    _ = ∫ w, ∫ v, ψ (q w) * (conj (a v) *
        WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d)
          f.val (HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu v u).val w) ∂ν ∂ν := by
      unfold WeakWeylGaussian.Construction.weakWeylGaussian
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        dsimp only
        rw [WeylSynthesis.Construction.weylMatrixCoefficient_synthesized_output RealFourierUnitary.Construction.real_nondiscrete ψ hc hu ν a a.continuous
          a.integrable f u h hh w, integral_const_mul]
    _ = ∫ v, ∫ w, ψ (q w) * (conj (a v) *
        WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d)
          f.val (HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu v u).val w) ∂ν ∂ν :=
      (integral_integral_swap hki).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        dsimp only [WeakWeylGaussian.Construction.weakWeylGaussian]
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun w => by dsimp only; ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeakSynthesis.Construction
