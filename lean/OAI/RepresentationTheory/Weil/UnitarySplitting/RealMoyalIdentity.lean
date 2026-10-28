import OAI.RepresentationTheory.Weil.UnitarySplitting.RealReconstructionHaar
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesis

/-! # Real Moyal Identity -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealMoyalIdentity.Construction

noncomputable section

section

/-! Real Weyl analysis and positive reconstruction on the actual test space. -/

open _root_.MeasureTheory
open scoped SchwartzMap ComplexConjugate

variable {d : ℕ} (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t))
variable (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]

include hc hu hn in
theorem exists_real_weyl_analysis_schwartz (u f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    ∃ A : SchwartzMap (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) ℂ, ∀ v,
      A v = WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val v := by
  obtain ⟨C, hC⟩ := RealWeylCoefficients.Construction.exists_real_weyl_coefficient_schwartz ψ hc hu hn (Weak.Construction.referencePositionMeasure ℝ d) u f
  refine ⟨SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap C, fun v => ?_⟩
  change conj (C v) = conj (WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val v)
  rw [hC]

include hc hu hn in
theorem realTest_reconstruction_positive (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) (hu0 : u ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d, ∀ x,
      WeylSynthesisAdd.Construction.weylSynthesis ψ ν (WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val) u.val x =
        (r : ℂ) * f.val x := by
  obtain ⟨a, ha, rfl⟩ := RealFourier.Construction.continuous_nontrivial_real_character ψ hc hu hn
  let U := (RealFourier.Construction.realSchwartzEquiv d).symm u
  have hU : U ≠ 0 := by
    intro hz
    apply hu0
    have hh := congrArg (RealFourier.Construction.realSchwartzEquiv d) hz
    simpa only [U, LinearEquiv.apply_symm_apply, map_zero] using hh
  obtain ⟨r, hr, hrec⟩ := RealReconstructionHaar.Construction.realWeyl_reconstruction_haar a ha (Weak.Construction.referencePositionMeasure ℝ d) ν U hU
  refine ⟨r, hr, fun f x => ?_⟩
  let F := (RealFourier.Construction.realSchwartzEquiv d).symm f
  have hh := hrec F x
  have hUf : (U : Local.FunctionsMetaplectic.Construction.Position ℝ d → ℂ) = u.val := funext (RealFourier.Construction.realSchwartzEquiv_symm_apply u)
  have hFf : (F : Local.FunctionsMetaplectic.Construction.Position ℝ d → ℂ) = f.val := funext (RealFourier.Construction.realSchwartzEquiv_symm_apply f)
  change WeylSynthesisAdd.Construction.weylSynthesis (RealFourier.Construction.realCharacter a) ν
    (WeylAnalysis.Construction.weylAnalysis (RealFourier.Construction.realCharacter a) (Weak.Construction.referencePositionMeasure ℝ d) (U : Local.FunctionsMetaplectic.Construction.Position ℝ d → ℂ) (F : Local.FunctionsMetaplectic.Construction.Position ℝ d → ℂ))
    (U : Local.FunctionsMetaplectic.Construction.Position ℝ d → ℂ) x = (r : ℂ) * (F : Local.FunctionsMetaplectic.Construction.Position ℝ d → ℂ) x at hh
  rwa [hUf, hFf] at hh

end

/-! The real Weyl analysis energy identity follows from positive reconstruction. -/

open _root_.MeasureTheory
open scoped SchwartzMap ComplexConjugate

theorem realWeyl_moyal_of_reconstruction {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) (r : ℝ)
    (hrec : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d, ∀ x,
      WeylSynthesisAdd.Construction.weylSynthesis ψ ν (WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val) u.val x =
        (r : ℂ) * f.val x)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    (∫ v, ‖WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val v‖ ^ 2 ∂ν) =
      r * Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f := by
  obtain ⟨A, hA⟩ := exists_real_weyl_analysis_schwartz ψ hc hu hn u f
  have hAa : (A : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℂ) = WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val := funext hA
  have hp := WeylSynthesis.Construction.weylSynthesis_pairing ψ hc hu (Weak.Construction.referencePositionMeasure ℝ d) ν A A.continuous A.integrable u f
  have hleft : (∫ x, WeylSynthesisAdd.Construction.weylSynthesis ψ ν A u.val x * conj (f.val x) ∂ Weak.Construction.referencePositionMeasure ℝ d) =
      (r : ℂ) * (Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f : ℂ) := by
    rw [hAa]
    simp_rw [hrec]
    have heq (x : Local.FunctionsMetaplectic.Construction.Position ℝ d) : (r : ℂ) * f.val x * conj (f.val x) =
        (r : ℂ) * ((‖f.val x‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [heq]
    rw [integral_const_mul, integral_complex_ofReal]
    rfl
  have hright : (∫ v, A v * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val v ∂ν) =
      ((∫ v, ‖WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val v‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    have heq (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) : A v * WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val v =
        ((‖WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val v‖ ^ 2 : ℝ) : ℂ) := by
      rw [hA]
      simp only [WeylAnalysis.Construction.weylAnalysis, RCLike.norm_conj, Complex.conj_mul', Complex.ofReal_pow]
    simp_rw [heq]
    exact integral_complex_ofReal
  rw [hleft, hright] at hp
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul]
  exact hp.symm

theorem realWeyl_moyal_positive {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) (hu0 : u ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d,
      (∫ v, ‖WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val f.val v‖ ^ 2 ∂ν) =
        r * Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f := by
  obtain ⟨r, hr, hrec⟩ := realTest_reconstruction_positive ψ hc hu hn ν u hu0
  exact ⟨r, hr, realWeyl_moyal_of_reconstruction ψ hc hu hn ν u r hrec⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealMoyalIdentity.Construction
