import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntrinsicComparison
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicAbelianTorusModel

/-! # Riemann Realization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RiemannRealization.CM.Abelian

noncomputable section

/-! Generic polarized rational weight-one realization, derived from the exact RiemannProjectivity input. -/

open scoped _root_.Manifold ContDiff

/-- RiemannProjectivity, the constructed lattice, algebraization, and actual H¹ comparison
give the generic Riemann realization required by CMReduction. -/
theorem riemannH1Realization_of_RiemannProjectivity (hRiemannProjectivity : ProjectiveTorusData.CM.Abelian.RiemannProjectivityInput)
    (U : Type) [AddCommGroup U] [Module ℚ U] : ComplexMultiplication.CMKnownResults.CM.KnownResults.RiemannH1Realization U := by
  intro H ⟨P⟩
  let : Module.Finite ℚ U := H.finiteDimensional
  let b := Module.finBasis ℚ U
  let D := ProjectiveTorusData.CM.Abelian.ProjectivePeriodData.ofHodgeStructure b H P hRiemannProjectivity
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicAbelianTorusModel.CM.Algebraization.AbelianTorusModel.exists_abelian_model D
  let e' : D.periodTorus ≃ₘ⟮𝓘(ℂ, D.space), 𝓘(ℂ, A.variety.analyticModel)⟯
      A.variety.analyticSpace := e
  exact ⟨{
    abelianVariety := A
    comparison := IntrinsicComparison.CM.Abelian.rationalComparison b H P hRiemannProjectivity A.variety e'
    holomorphic := IntrinsicComparison.CM.Abelian.holomorphic b H P hRiemannProjectivity A e'
    antiholomorphic := IntrinsicComparison.CM.Abelian.antiholomorphic b H P hRiemannProjectivity A e'
  }⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.RiemannRealization.CM.Abelian
