import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayley
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyOperator

/-! # Real Cayley Operator -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyOperator.Construction

noncomputable section

/-! The nonzero real Cayley operator on the actual Bruhat space. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

variable {d : ℕ} (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t))
variable (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
variable (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
variable (g : FrameTransport.Construction.StandardSymplectic ℝ d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)
variable (hD : ∀ x, D x = g.val x - x)

def realCayleyVector (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d :=
  Classical.choose (RealCayley.Construction.realCayley_representable ψ hc hu hn ν g D hD f)

theorem realCayleyVector_pairing (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    ⟪Weak.Construction.testToL2 ℝ d h, Weak.Construction.testToL2 ℝ d (realCayleyVector ψ hc hu hn ν g D hD f)⟫_ℂ =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν
        (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) D) f.val h.val :=
  Classical.choose_spec (RealCayley.Construction.realCayley_representable ψ hc hu hn ν g D hD f) h

def realCayleyOperator : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d where
  toFun := realCayleyVector ψ hc hu hn ν g D hD
  map_add' f k := by
    apply UltraCayleyOperator.Construction.testPairing_ext
    intro h
    rw [realCayleyVector_pairing, map_add, inner_add_right,
      realCayleyVector_pairing, realCayleyVector_pairing]
    exact RealWeakGaussian.Construction.weakWeylGaussian_add_left_real ψ hc hu hn ν _ (RealCayleySchwartz.Construction.realCayleyWeylPhase_temperate D).1.continuous f k h
  map_smul' z f := by
    apply UltraCayleyOperator.Construction.testPairing_ext
    intro h
    rw [realCayleyVector_pairing, map_smul, inner_smul_right, realCayleyVector_pairing]
    exact WeakGaussianLinearity.Construction.weakWeylGaussian_smul_left RealFourierUnitary.Construction.real_nondiscrete ψ hc hu ν _ z f h

theorem realCayleyOperator_pairing (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    ⟪Weak.Construction.testToL2 ℝ d h, Weak.Construction.testToL2 ℝ d (realCayleyOperator ψ hc hu hn ν g D hD f)⟫_ℂ =
      WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν
        (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) D) f.val h.val :=
  realCayleyVector_pairing ψ hc hu hn ν g D hD f h

theorem realCayleyOperator_ne_zero : realCayleyOperator ψ hc hu hn ν g D hD ≠ 0 := by
  obtain ⟨f, h, hne⟩ := RealWeakGaussian.Construction.weakWeylGaussian_nonzero_real ψ hc hu hn ν _ (RealCayleySchwartz.Construction.realCayleyWeylPhase_temperate D).1.continuous
  intro hz
  apply hne
  rw [← realCayleyOperator_pairing ψ hc hu hn ν g D hD, hz]
  simp only [LinearMap.zero_apply, map_zero, inner_zero_right]

theorem realCayleyOperator_intertwines (w : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    realCayleyOperator ψ hc hu hn ν g D hD (HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu w f) =
      HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu (g.val w) (realCayleyOperator ψ hc hu hn ν g D hD f) := by
  apply UltraCayleyOperator.Construction.testPairing_ext
  intro h
  rw [realCayleyOperator_pairing, WeakCayleyCoefficients.Construction.weakCayleyGaussian_intertwines RealFourierUnitary.Construction.real_nondiscrete ψ hc hu ν g D hD,
    ← realCayleyOperator_pairing ψ hc hu hn ν g D hD]
  exact (Weyl.Construction.heisenbergOperator_adjoint RealFourierUnitary.Construction.real_nondiscrete ψ hc hu (g.val w)
    (realCayleyOperator ψ hc hu hn ν g D hD f) h).symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyOperator.Construction
