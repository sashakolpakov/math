import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyOperator
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase

/-! # Ultra Cayley Matrix Coefficient -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyMatrixCoefficient.Construction

noncomputable section

/-! Matrix coefficients of the actual Cayley operator are explicit
bilinear Fourier transforms of compact Weyl coefficients. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

theorem ultraCayleyOperator_matrixCoefficient
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [IsUltrametricDist F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (hn : ∃ x : F, ψ x ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic F d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (hD : ∀ x, D x = g.val x - x) (f k : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) :
    WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d)
      (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g D hD f).val k.val v =
      ψ (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D v) *
        ∫ x, ψ (StandardTransvections.Construction.standardSymplecticBilinear F d (-(D.symm v)) x) *
          (ψ (CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D x) *
            WeylMatrixCoefficients.Construction.weylMatrixCoefficient ψ (Weak.Construction.referencePositionMeasure F d) f.val k.val x) ∂ν := by
  rw [WeylMatrixCoefficients.Construction.weylMatrixCoefficient_eq_inner hF ψ hc hu, Weyl.Construction.heisenbergOperator_adjoint,
    UltraCayleyOperator.Construction.ultraCayleyOperator_pairing,
    WeakCayleyCoefficients.Construction.weakCayleyGaussian_output_coefficient hF ψ hc hu ν g D hD,
    CayleyCompositionPhase.Construction.cayleyWeylPhase_neg, map_neg]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyMatrixCoefficient.Construction
