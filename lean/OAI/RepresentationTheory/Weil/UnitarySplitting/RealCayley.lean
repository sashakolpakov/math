import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleySchwartz
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealWeakSynthesis
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealMoyalIdentity
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianLinearity

/-! # Real Cayley -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayley.Construction

noncomputable section

/-! Real weak Cayley forms are represented by actual Bruhat test vectors. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem realCayley_representable {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic ℝ d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)
    (hD : ∀ x, D x = g.val x - x) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    ∃ w : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d, ∀ h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d,
      ⟪Weak.Construction.testToL2 ℝ d h, Weak.Construction.testToL2 ℝ d w⟫_ℂ =
        WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν
          (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) D) f.val h.val := by
  obtain ⟨u, hu0⟩ := LocalTest.Construction.exists_test_nonzero_of_real_coordinates (ContinuousAddEquiv.refl (Local.FunctionsMetaplectic.Construction.Position ℝ d))
  obtain ⟨r, hr, hrec⟩ := RealMoyalIdentity.Construction.realTest_reconstruction_positive ψ hc hu hn ν u hu0
  obtain ⟨b, hb⟩ := RealCayleySchwartz.Construction.exists_real_cayley_coefficient_schwartz ψ hc hu hn ν g D hD f u
  let w : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d := ⟨WeylSynthesisAdd.Construction.weylSynthesis ψ ν b u.val, RealWeylFourier.Construction.weylSynthesis_mem_real ψ hc hu ν b u⟩
  let q := CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) D
  have hq : Continuous q := (RealCayleySchwartz.Construction.realCayleyWeylPhase_temperate D).1.continuous
  refine ⟨(r : ℂ)⁻¹ • w, fun h => ?_⟩
  obtain ⟨A, hA⟩ := RealMoyalIdentity.Construction.exists_real_weyl_analysis_schwartz ψ hc hu hn u h
  have hAa : (A : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℂ) = WeylAnalysis.Construction.weylAnalysis ψ (Weak.Construction.referencePositionMeasure ℝ d) u.val h.val := funext hA
  have hh : ((r : ℂ) • h).val = WeylSynthesisAdd.Construction.weylSynthesis ψ ν A u.val := by
    rw [hAa]
    funext x
    exact (hrec h x).symm
  have hp : ⟪Weak.Construction.testToL2 ℝ d h, Weak.Construction.testToL2 ℝ d w⟫_ℂ =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν q f.val ((r : ℂ) • h).val := by
    rw [RealWeakSynthesis.Construction.realWeakWeylGaussian_synthesized_output ψ hc hu hn ν q hq A f u ((r : ℂ) • h) hh,
      Weak.Construction.testToL2_inner]
    change (∫ x, WeylSynthesisAdd.Construction.weylSynthesis ψ ν b u.val x * conj (h.val x) ∂ Weak.Construction.referencePositionMeasure ℝ d) = _
    rw [WeylSynthesis.Construction.weylSynthesis_pairing ψ hc hu (Weak.Construction.referencePositionMeasure ℝ d) ν b b.continuous b.integrable u h]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      dsimp only
      rw [hA, hb]
      simp only [WeylAnalysis.Construction.weylAnalysis, starRingEnd_self_apply]
      exact mul_comm _ _
  rw [map_smul, inner_smul_right, hp,
    WeakGaussianLinearity.Construction.weakWeylGaussian_smul_right RealFourierUnitary.Construction.real_nondiscrete ψ hc hu, Complex.conj_ofReal,
    ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_mul]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayley.Construction
