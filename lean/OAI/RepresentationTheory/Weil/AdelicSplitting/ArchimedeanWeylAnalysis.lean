import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanSpace
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPhasePlancherel
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylEnergy
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedWeakAnalysis
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanFourier
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylAnalysis

/-! # Archimedean Weyl Analysis -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylAnalysis.Construction

noncomputable section

/-! Weyl analysis is a concrete linear map into L² of phase space.
Its pairings follow from the proved energy identity by polarization. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
variable [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
variable (hk : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
variable (W : Oscillator.Construction.LocalCover k N ψ) (hW : Oscillator.Construction.localProjection k N ψ W = Local.Generators.Construction.weylSymplectic k N)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) [ν.IsAddHaarMeasure] (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)

include hk hc hu W hW

theorem archimedeanWeylAnalysis_memLp (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    MemLp (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val) 2 ν := by
  let C := ArchimedeanWeylCoefficients.LocalAnalysis.archimedeanWeylCoefficientRapid hk ψ hc hu W hW u f
  exact (C.memLp_two ν).star

def archimedeanWeylAnalysisToL2 : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N →ₗ[ℂ] Lp ℂ 2 ν where
  toFun f := (archimedeanWeylAnalysis_memLp hk ψ hc hu W hW ν u f).toLp
    (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val)
  map_add' f h := by
    simp only [UnitarySplitting.WeylAnalysis.Construction.weylAnalysis_add hk ψ hc hu]
    exact MemLp.toLp_add _ _
  map_smul' z f := by
    simp only [UnitarySplitting.WeylAnalysis.Construction.weylAnalysis_smul hk ψ hc hu]
    exact MemLp.toLp_const_smul _ _

theorem archimedeanWeylAnalysisToL2_ae (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u f =ᵐ[ν]
      UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val :=
  (archimedeanWeylAnalysis_memLp hk ψ hc hu W hW ν u f).coeFn_toLp

theorem archimedeanWeylAnalysisToL2_inner (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ⟪archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u f,
      archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u h⟫_ℂ =
    ∫ v, UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val h.val v *
      conj (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val v) ∂ν := by
  change (∫ v, ⟪(archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u f) v,
    (archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u h) v⟫_ℂ ∂ν) = _
  apply integral_congr_ae
  filter_upwards [archimedeanWeylAnalysisToL2_ae hk ψ hc hu W hW ν u f,
    archimedeanWeylAnalysisToL2_ae hk ψ hc hu W hW ν u h] with v hf hh
  rw [hf, hh]
  rfl

variable (hMoyal : ∀ f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
  (∫ v, ‖UnitarySplitting.WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) f.val h.val v‖ ^ 2 ∂ν) =
    Local.FunctionsMetaplectic.Construction.l2Energy k N f * Local.FunctionsMetaplectic.Construction.l2Energy k N h)

include hMoyal in
theorem archimedeanWeylAnalysisToL2_norm_sq (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    ‖archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u f‖ ^ 2 =
      Local.FunctionsMetaplectic.Construction.l2Energy k N u * Local.FunctionsMetaplectic.Construction.l2Energy k N f := by
  rw [archimedeanWeylAnalysisToL2, LinearMap.coe_mk, AddHom.coe_mk, NonarchimedeanFourier.LocalAnalysis.toLp_norm_sq]
  simp only [UnitarySplitting.WeylAnalysis.Construction.weylAnalysis, RCLike.norm_conj]
  exact hMoyal u f

include hMoyal in
theorem archimedeanWeylAnalysis_pairing (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ v, UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val h.val v *
      conj (UnitarySplitting.WeylAnalysis.Construction.weylAnalysis ψ (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) u.val f.val v) ∂ν) =
    (Local.FunctionsMetaplectic.Construction.l2Energy k N u : ℂ) * ∫ x, h.val x * conj (f.val x) ∂ UnitarySplitting.Weak.Construction.referencePositionMeasure k N := by
  let P := UnitarySplitting.Weak.Construction.testToL2 k N
  let M : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N →ₗ[ℂ] Lp ℂ 2 (UnitarySplitting.Weak.Construction.referencePositionMeasure k N) :=
    (Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N u) : ℂ) • P
  have hEu : 0 ≤ Local.FunctionsMetaplectic.Construction.l2Energy k N u := integral_nonneg (fun x => sq_nonneg ‖u.val x‖)
  have hnorm (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
      ‖archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u f‖ ^ 2 = ‖M f‖ ^ 2 := by
    rw [archimedeanWeylAnalysisToL2_norm_sq hk ψ hc hu W hW ν u hMoyal]
    change _ = ‖(Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N u) : ℂ) • P f‖ ^ 2
    rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hEu]
    congr 1
    rw [UnitarySplitting.Weak.Construction.testToL2_norm]
    exact (Real.sq_sqrt (show 0 ≤ Local.FunctionsMetaplectic.Construction.l2Energy k N f from
      integral_nonneg (fun x => sq_nonneg ‖f.val x‖))).symm
  have hp := ArchimedeanSpace.Construction.inner_eq_of_linear_norm_sq_eq
    (archimedeanWeylAnalysisToL2 hk ψ hc hu W hW ν u) M hnorm f h
  rw [archimedeanWeylAnalysisToL2_inner] at hp
  rw [hp]
  change ⟪(Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N u) : ℂ) • P f,
    (Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy k N u) : ℂ) • P h⟫_ℂ = _
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hEu, UnitarySplitting.Weak.Construction.testToL2_inner]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanWeylAnalysis.Construction
