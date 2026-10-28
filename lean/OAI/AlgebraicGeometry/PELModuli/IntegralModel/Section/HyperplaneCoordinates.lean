import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions

/-! # Hyperplane Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.HyperplaneCoordinates

noncomputable section

/-! The section-defined projective map pulls the actual hyperplane chart
equations back to the original ratios of sections. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages
universe u
variable {R : Type u} [CommRing R] {T S X : Scheme.{u}} {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveChartOpenMap (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤))
    (i : Fin (n + 1)) (hi : v i = 1) :
    T ⟶ (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi)) ≫
    (Proj.basicOpenIsoSpec (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one).inv

theorem projectiveChartOpenMap_ι (c : R →+* Γ(T, ⊤)) (v : Fin (n + 1) → Γ(T, ⊤))
    (i : Fin (n + 1)) (hi : v i = 1) :
    projectiveChartOpenMap c v i hi ≫ (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι =
      AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartMap c v i hi := by
  simp only [projectiveChartOpenMap, AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartMap, Proj.awayι, Category.assoc]

theorem projectiveChartOpenMap_equation (c : R →+* Γ(T, ⊤))
    (v : Fin (n + 1) → Γ(T, ⊤)) (i : Fin (n + 1)) (hi : v i = 1)
    (j : Fin (n + 1)) :
    (projectiveChartOpenMap c v i hi).appTop
      ((SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).topIso.inv
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j)) = v j := by
  let U := SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i
  let e := Proj.basicOpenIsoSpec (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one
  let z : AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R n i := HomogeneousLocalization.Away.isLocalizationElem
    (MvPolynomial.isHomogeneous_X R i) (MvPolynomial.isHomogeneous_X R j)
  have he : e.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R n i))).inv z) =
      U.topIso.inv (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j) := by
    rw [SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_eq_isLocalizationElem]
    change (Proj.basicOpenToSpec (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)).app ⊤
      ((Scheme.ΓSpecIso _).inv z) = _
    rw [Proj.basicOpenToSpec_app_top]
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
    rfl
  rw [← he]
  change (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi)) ≫ e.inv).appTop
    (e.hom.appTop ((Scheme.ΓSpecIso _).inv z)) = _
  rw [← elementwise_of% Scheme.Hom.comp_appTop]
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
  have hc : (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R n i))).hom ≫
        CommRingCat.ofHom (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi) := by
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality]
  rw [hc]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  change AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi z = v j
  simpa only [z, HomogeneousLocalization.Away.isLocalizationElem, pow_one] using
    AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartEvaluation_coordinate c v i hi j

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.HyperplaneCoordinates
