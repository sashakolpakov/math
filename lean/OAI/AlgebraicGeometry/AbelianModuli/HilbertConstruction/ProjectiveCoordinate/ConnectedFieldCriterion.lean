import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalFunctionDimension
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PointedFamilyFiberConnectedness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PropertyComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.MatrixRankScalarExtension
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange

/-! # Connected Field Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.ConnectedFieldCriterion

noncomputable section

/-! An actual matrix model of global functions detects geometric connectedness of a pointed proper smooth projective quotient over each coefficient field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert

universe u

theorem projectiveCoordinate_connected_field_kernel
    {R K : Type u} [CommRing R] [Field K] [Algebra R K] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    [IsProper (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))] [Smooth (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    (x : Spec (.of R) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) (hx : x ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) = 𝟙 _)
    {μ ν : Type u} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
    (B : Matrix ν μ R)
    (e : Coefficient.AlgebraPresheaf.coefficientAlgebraSections
      (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I)))) ⊤ ≃ₗ[K]
      (Matrix.toLin' (B.map (algebraMap R K))).ker) :
    GeometricallyConnected (pullback.snd (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ↔
      Module.finrank K (Matrix.toLin' (B.map (algebraMap R K))).ker ≤ 1 := by
  let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
  let c := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let pK := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I))
  let H := HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := K) I
  have : IsProper pK :=
    (inferInstance : MorphismProperty.IsStableUnderBaseChange (@IsProper : MorphismProperty Scheme.{u})).of_isPullback
      H (inferInstance : IsProper p)
  have : Smooth pK := smooth_isStableUnderBaseChange.of_isPullback H (inferInstance : Smooth p)
  let xK := PointedFamilyFiberConnectedness.schemeSectionBaseChange p x hx c ≫ H.isoPullback.inv
  have hxK : xK ≫ pK = 𝟙 _ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => PointedFamilyFiberConnectedness.schemeSectionBaseChange p x hx c ≫ f) H.isoPullback_inv_snd).trans
        (PointedFamilyFiberConnectedness.schemeSectionBaseChange_section p x hx c))
  have : Module.Finite K (Coefficient.AlgebraPresheaf.coefficientAlgebraSections (Affine.ChartCoefficientSections.schemeGlobalCoefficient pK) ⊤) := Module.Finite.equiv e.symm
  have hg : GeometricallyConnected pK ↔ GeometricallyConnected (pullback.snd p c) :=
    Cartesian.PropertyComparison.property_cartesian_iff_pullback (@GeometricallyConnected : MorphismProperty Scheme.{u})
      (HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := K) I) pK p c H
  exact hg.symm.trans ((Coefficient.GlobalFunctionDimension.properSmoothPointed_connected_iff_coefficient_dimension_le_one pK xK hxK).trans
    (congrArg (fun q : ℕ => q ≤ 1) e.finrank_eq).to_iff)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.ConnectedFieldCriterion
