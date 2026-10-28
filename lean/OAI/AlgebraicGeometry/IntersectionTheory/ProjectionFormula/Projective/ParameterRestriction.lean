import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterInfinity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportClosure

/-! # Parameter Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterRestriction

noncomputable section

/-! A projective parameter restricts through the actual generic-stalk
field map, and its positive fiber coefficients agree on every open chart. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Y Z : Scheme} [IsIntegral Y] [IsIntegral Z]
  (i : Y ⟶ Z) [IsOpenImmersion i] (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
  (hη : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

include hη in
theorem generic : (i ≫ t) (genericPoint Y) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) :=
  (congrArg t (genericPoint_eq_of_isOpenImmersion i)).trans hη

theorem field : Divisor.DivisorRestriction.openFieldMap i (LineParameter.pullback t hη) =
    LineParameter.pullback (i ≫ t) (generic i t hη) := by
  unfold LineParameter.pullback Divisor.DivisorRestriction.openFieldMap
  rw [Generic.Fields.genericFieldMap_comp i t (genericPoint_eq_of_isOpenImmersion i) hη]
  rfl

theorem shifted_field (a : ℂ) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    Divisor.DivisorRestriction.openFieldMap i
      (LineParameter.pullback t hη - algebraMap ℂ Z.functionField a) =
      LineParameter.pullback (i ≫ t) (generic i t hη) -
        algebraMap ℂ Y.functionField a := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  rw [map_sub, field]
  congr 1
  change (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i (genericPoint_eq_of_isOpenImmersion i)).hom
      (Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) a) =
    Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) a
  rw [Category.assoc]
  exact DFunLike.congr_fun (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap_scalar i
    (genericPoint_eq_of_isOpenImmersion i) (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)) a

theorem order [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] (a : ℂ) (y : Y) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    Y.ord (LineParameter.pullback (i ≫ t) (generic i t hη) -
      algebraMap ℂ Y.functionField a) y =
    Z.ord (LineParameter.pullback t hη - algebraMap ℂ Z.functionField a) (i y) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  rw [← shifted_field i t hη a]
  exact Divisor.DivisorRestriction.ord_openImmersion i _ y

theorem positive [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Z]
    (a : ℂ) (y : Y) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Y
      (LineParameter.pullback (i ≫ t) (generic i t hη) -
        algebraMap ℂ Y.functionField a)) y =
    PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z
      (LineParameter.pullback t hη - algebraMap ℂ Z.functionField a)) (i y) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  simp only [PositiveCycle.positivePart_apply, Affine.DivisorNorm.rationalPrincipalDivisor_apply,
    order i t hη a y]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterRestriction
