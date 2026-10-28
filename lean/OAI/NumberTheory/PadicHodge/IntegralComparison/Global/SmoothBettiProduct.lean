import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SmoothCohomologyCup
import OAI.AlgebraicGeometry.AbelianVariety.GeometricCup

/-! # Smooth Betti Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SmoothBettiProduct

noncomputable section

/-! The original global smooth de Rham/Betti comparison preserves
products, by the genuine smooth-simplex integration homotopy. -/

theorem comparison_cup (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology V.analyticModel V.analyticSpace p)
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology V.analyticModel V.analyticSpace q) :
    (V.deRhamBettiIso (p + q)).hom
        (SmoothCohomologyCup.cohomologyCup V.analyticModel V.analyticSpace p q a b) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver) p q
        ((V.deRhamBettiIso p).hom a) ((V.deRhamBettiIso q).hom b) := by
  obtain ⟨a, rfl⟩ := Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_surjective V.analyticModel V.analyticSpace p a
  obtain ⟨b, rfl⟩ := Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_surjective V.analyticModel V.analyticSpace q b
  rw [SmoothCohomologyCup.cup_formClass]
  apply AlgebraicGeometry.AbelianVariety.GeometricProduct.Constructions.ExteriorCohomology.bettiToSmoothSingular_injective V (p + q)
  rw [AlgebraicGeometry.AbelianVariety.GeometricProduct.Constructions.ExteriorCohomology.bettiToSmoothSingular_cup, V.deRhamBettiIso_formClass,
    V.deRhamBettiIso_formClass, V.deRhamBettiIso_formClass]
  exact AlgebraicGeometry.AbelianVariety.IntegrationProduct.Constructions.ExteriorCohomology.integration_class_wedge a b

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SmoothBettiProduct
