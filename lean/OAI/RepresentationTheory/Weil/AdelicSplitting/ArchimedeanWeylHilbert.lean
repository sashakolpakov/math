import OAI.RepresentationTheory.Weil.AdelicSplitting.DenseExtension
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylAnalysis

/-! # Archimedean Weyl Hilbert -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylHilbert.Construction

noncomputable section

/-! The actual Weyl analysis map extends to the reference Hilbert space,
with its exact norm and almost-everywhere coefficient formula. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure] (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
variable (hMoyal : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
  (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v‖ ^ 2 ∂ν) =
    Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N h)

include hMoyal in
theorem archimedeanWeylAnalysisToL2_bound (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ‖ArchimedeanWeylAnalysis.Construction.archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u f‖ ≤
      Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N u) * ‖UnitarySplitting.Weak.Construction.testToL2 k N f‖ := by
  apply le_of_eq
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [ArchimedeanWeylAnalysis.Construction.archimedeanWeylAnalysisToL2_norm_sq hk ψ hc hu W hW ν u hMoyal,
    mul_pow, Real.sq_sqrt (show 0 ≤ Local.FunctionsMetaplectic.Construction.l2Energy k N u from
      integral_nonneg (fun x => sq_nonneg ‖u.val x‖)),
    UnitarySplitting.Weak.Construction.testToL2_norm,
    Real.sq_sqrt (show 0 ≤ Local.FunctionsMetaplectic.Construction.l2Energy k N f from integral_nonneg (fun x => sq_nonneg ‖f.val x‖))]

def archimedeanWeylHilbertAnalysis :
    Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) →L[ℂ] Lp ℂ 2 ν :=
  (ArchimedeanWeylAnalysis.Construction.archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u).extendOfNorm
    (UnitarySplitting.Weak.Construction.testToL2 k N)

include hMoyal in
theorem archimedeanWeylHilbertAnalysis_test (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    archimedeanWeylHilbertAnalysis hk ψ hc hu W hW ν u
        (UnitarySplitting.Weak.Construction.testToL2 k N f) =
      ArchimedeanWeylAnalysis.Construction.archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u f :=
  LinearMap.extendOfNorm_eq (ArchimedeanSpace.Construction.archimedean_testToL2_dense N)
    ⟨_, archimedeanWeylAnalysisToL2_bound hk ψ hc hu W hW ν u hMoyal⟩ f

include hMoyal in
theorem archimedeanWeylHilbertAnalysis_norm_sq (x : Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)) :
    ‖archimedeanWeylHilbertAnalysis hk ψ hc hu W hW ν u x‖ ^ 2 =
      Local.FunctionsMetaplectic.Construction.l2Energy k N u * ‖x‖ ^ 2 := by
  apply DenseExtension.Construction.dense_linear_extension_norm_sq (UnitarySplitting.Weak.Construction.testToL2 k N)
    (ArchimedeanSpace.Construction.archimedean_testToL2_dense N) _ _ _
    (archimedeanWeylAnalysisToL2_bound hk ψ hc hu W hW ν u hMoyal)
  intro f
  rw [ArchimedeanWeylAnalysis.Construction.archimedeanWeylAnalysisToL2_norm_sq hk ψ hc hu W hW ν u hMoyal,
    UnitarySplitting.Weak.Construction.testToL2_norm,
    Real.sq_sqrt (show 0 ≤ Local.FunctionsMetaplectic.Construction.l2Energy k N f from integral_nonneg (fun y => sq_nonneg ‖f.val y‖))]

include hMoyal in
theorem archimedeanWeylHilbertAnalysis_ae (x : Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)) :
    archimedeanWeylHilbertAnalysis hk ψ hc hu W hW ν u x =ᵐ[ν]
      fun v => ⟪UnitarySplitting.Weak.Construction.testToL2 k N (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u), x⟫_ℂ := by
  apply DenseExtension.Construction.dense_linear_extension_ae (UnitarySplitting.Weak.Construction.testToL2 k N)
    (ArchimedeanSpace.Construction.archimedean_testToL2_dense N) ν _ _
    (archimedeanWeylAnalysisToL2_bound hk ψ hc hu W hW ν u hMoyal)
    _ (fun v => by fun_prop)
  intro f
  filter_upwards [ArchimedeanWeylAnalysis.Construction.archimedeanWeylAnalysisToL2_ae hk ψ hc hu W hW ν u f] with v hv
  exact hv.trans (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis_eq_inner hk ψ hc hu u f v)

include W hW hMoyal in
theorem archimedeanWeylHilbert_coefficient_energy (x : Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N)) :
    (∫ v, ‖⟪UnitarySplitting.Weak.Construction.testToL2 k N
      (UnitarySplitting.HeisenbergStability.Construction.heisenbergOperator hk ψ hc hu v u), x⟫_ℂ‖ ^ 2 ∂ν) =
        Local.FunctionsMetaplectic.Construction.l2Energy k N u * ‖x‖ ^ 2 := by
  calc
    _ = ∫ v, ‖archimedeanWeylHilbertAnalysis hk ψ hc hu W hW ν u x v‖ ^ 2 ∂ν := by
      apply integral_congr_ae
      filter_upwards [archimedeanWeylHilbertAnalysis_ae hk ψ hc hu W hW ν u hMoyal x] with v hv
      rw [hv]
    _ = ‖archimedeanWeylHilbertAnalysis hk ψ hc hu W hW ν u x‖ ^ 2 := NonarchimedeanFourier.LocalAnalysis.L2_integral_norm_sq_general ν _
    _ = _ := archimedeanWeylHilbertAnalysis_norm_sq hk ψ hc hu W hW ν u hMoyal x

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylHilbert.Construction
