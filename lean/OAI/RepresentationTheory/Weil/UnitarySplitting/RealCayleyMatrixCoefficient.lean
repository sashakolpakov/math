import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyOperator
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase

/-! # Real Cayley Matrix Coefficient -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyMatrixCoefficient.Construction

noncomputable section

/-! Matrix coefficients of the actual Cayley operator are explicit
bilinear Fourier transforms of Schwartz Weyl coefficients. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

theorem realCayleyOperator_matrixCoefficient
    {d : ℕ} (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun x : ℝ => ψ x)) (hu : ∀ x : ℝ, ‖ψ x‖ = 1)
    (hn : ∃ x : ℝ, ψ x ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic ℝ d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)
    (hD : ∀ x, D x = g.val x - x) (f k : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) :
    WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d)
      (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD f).val k.val v =
      ψ (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) D v) *
        ∫ x, ψ (StandardTransvections.Construction.standardSymplecticBilinear ℝ d (-(D.symm v)) x) *
          (ψ (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) D x) *
            WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure ℝ d) f.val k.val x) ∂ν := by
  rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner RealFourierUnitary.Construction.real_nondiscrete ψ hc hu, Weyl.Construction.heisenbergOperator_adjoint,
    RealCayleyOperator.Construction.realCayleyOperator_pairing,
    WeakCayleyCoefficients.Construction.weakCayleyGaussian_output_coefficient RealFourierUnitary.Construction.real_nondiscrete ψ hc hu ν g D hD,
    CayleyCompositionPhase.Construction.cayleyWeylPhase_neg, map_neg]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyMatrixCoefficient.Construction
