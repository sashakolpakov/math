import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ProjectiveParameter
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SpecStalkAlgebra

/-! # Parameter Comparison -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterComparison

noncomputable section

/-! The translated polynomial coordinate in affine stalks agrees
with the regular germ of the rational projective-line parameter. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Polynomial

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIs.MatrixParameterOpen

theorem affine_shift (x : Spec (.of ℂ[X])) (a : ℂ) :
    Projective.ParameterGerms.shiftedGerm Projective.FamilyIs.MatrixParameterOpen.affine x (ProjectiveParameter.contained x) a =
      StructureSheaf.toStalk ℂ[X] x (Polynomial.X - Polynomial.C a) := by
  unfold Projective.ParameterGerms.shiftedGerm
  rw [Projective.FamilyIs.MatrixParameterOpen.affine_over]
  let := Stalk.PointAlgebra.scalarAlgebra
    (Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* ℂ[X]))) x
  rw [ProjectiveParameter.finiteGerm, map_sub]
  congr 1
  exact (SpecStalkAlgebra.toStalk ℂ ℂ[X] x).commutes a |>.symm

variable {Z : Scheme} [IsIntegral Z] (t : Z ⟶ Spec (.of ℂ[X]))

omit [IsIntegral Z] in
theorem germ (x : Z) (a : ℂ) :
    Projective.ParameterGerms.shiftedGerm (t ≫ Projective.FamilyIs.MatrixParameterOpen.affine) x
      (ProjectiveParameter.contained (t x)) a = ParameterFiber.germ ℂ t x a := by
  let := Stalk.PointAlgebra.scalarAlgebra (Projective.FamilyIs.MatrixParameterOpen.affine ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) (t x)
  let := Stalk.PointAlgebra.scalarAlgebra (t ≫ (Projective.FamilyIs.MatrixParameterOpen.affine ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)) x
  have hc := (Stalk.ScalarMaps.stalk t (Projective.FamilyIs.MatrixParameterOpen.affine ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) x).commutes a
  have hf : Projective.ParameterGerms.finiteGerm (t ≫ Projective.FamilyIs.MatrixParameterOpen.affine) x
      (ProjectiveParameter.contained (t x)) =
      t.stalkMap x (Projective.ParameterGerms.finiteGerm Projective.FamilyIs.MatrixParameterOpen.affine (t x)
        (ProjectiveParameter.contained (t x))) :=
    GermPullback.fraction_comp 1 t Projective.FamilyIs.MatrixParameterOpen.affine x
      (Projective.LineParameter.RationalFractions.coordinate 1 1)
      (Projective.LineParameter.RationalFractions.coordinate 1 0) (ProjectiveParameter.contained (t x))
  change Projective.ParameterGerms.shiftedGerm (t ≫ Projective.FamilyIs.MatrixParameterOpen.affine) x _ a =
    t.stalkMap x (StructureSheaf.toStalk ℂ[X] (t x) (Polynomial.X - Polynomial.C a))
  rw [← affine_shift]
  unfold Projective.ParameterGerms.shiftedGerm
  rw [Category.assoc, hf, map_sub]
  exact congrArg (fun b => t.stalkMap x
    (Projective.ParameterGerms.finiteGerm Projective.FamilyIs.MatrixParameterOpen.affine (t x)
      (ProjectiveParameter.contained (t x))) - b) hc.symm

theorem field (hη : (t ≫ Projective.FamilyIs.MatrixParameterOpen.affine) (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (x : Z) (a : ℂ) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((t ≫ Projective.FamilyIs.MatrixParameterOpen.affine) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    algebraMap (Z.presheaf.stalk x) Z.functionField (ParameterFiber.germ ℂ t x a) =
      Projective.LineParameter.pullback (t ≫ Projective.FamilyIs.MatrixParameterOpen.affine) hη - algebraMap ℂ Z.functionField a := by
  rw [← germ]
  exact Projective.ParameterGerms.shiftedGerm_field (t ≫ Projective.FamilyIs.MatrixParameterOpen.affine) hη x
    (ProjectiveParameter.contained (t x)) a

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterComparison
