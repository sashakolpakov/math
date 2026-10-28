import OAI.AlgebraicGeometry.AbelianVariety.IntegrationProduct
import OAI.AlgebraicGeometry.AbelianVariety.GeometricProduct

/-! # Geometric Cup -/

namespace OAI.AlgebraicGeometry.AbelianVariety.GeometricCup.Constructions.ExteriorCohomology

noncomputable section

/-- The invariant-representative exterior product is the actual singular cup product. -/
theorem geometricBettiWedge_eq_cup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ)
    (a : A.variety.complexCohomology p) (b : A.variety.complexCohomology q) :
    GeometricProduct.Constructions.ExteriorCohomology.geometricBettiWedge A p q a b =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a b := by
  apply GeometricProduct.Constructions.ExteriorCohomology.bettiToSmoothSingular_injective A.variety (p + q)
  rw [GeometricProduct.Constructions.ExteriorCohomology.geometricBettiWedge_closedForm, A.variety.deRhamBettiIso_formClass,
    GeometricProduct.Constructions.ExteriorCohomology.bettiToSmoothSingular_cup]
  have ha := A.variety.deRhamBettiIso_formClass p (GeometricProduct.Constructions.ExteriorCohomology.abelianClosedRepresentative A p a)
  have hb := A.variety.deRhamBettiIso_formClass q (GeometricProduct.Constructions.ExteriorCohomology.abelianClosedRepresentative A q b)
  rw [GeometricProduct.Constructions.ExteriorCohomology.abelianClosedRepresentative_class] at ha hb
  rw [ha, hb]
  exact IntegrationProduct.Constructions.ExteriorCohomology.integration_class_wedge (GeometricProduct.Constructions.ExteriorCohomology.abelianClosedRepresentative A p a) (GeometricProduct.Constructions.ExteriorCohomology.abelianClosedRepresentative A q b)

end

end OAI.AlgebraicGeometry.AbelianVariety.GeometricCup.Constructions.ExteriorCohomology
