import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterGerms
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FormStalkComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NonunitParameterShift
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.InverseDivisorSupport

/-! # Parameter Infinity -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterInfinity

noncomputable section

/-! Scalar translates of a dominant projective-line parameter have
no positive divisor at points outside its finite coordinate chart. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Z : Scheme} [IsIntegral Z] (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
  (hη : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

omit [IsIntegral Z] in
theorem other_chart (x : Z) (hx : t x ∉ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) :
    t x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 1 := by
  obtain ⟨i, hi⟩ := Foundations.Scheme.ProjectiveCoordinateCover.exists_mem_projectiveCoordinateOpen 1 (t x)
  fin_cases i
  · exact (hx hi).elim
  · exact hi

def inverseGerm (x : Z) (hx : t x ∉ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) : Z.presheaf.stalk x :=
  t.stalkMap x (PointJets.StalkFractions.fraction 1 (t x)
    (LineParameter.RationalFractions.coordinate 1 0)
    (LineParameter.RationalFractions.coordinate 1 1) (other_chart t x hx))

theorem inverseGerm_field (x : Z) (hx : t x ∉ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) :
    algebraMap (Z.presheaf.stalk x) Z.functionField (inverseGerm t x hx) =
      (LineParameter.pullback t hη)⁻¹ := by
  rw [inverseGerm, ← Divisor.DivisorRestriction.genericFieldMap_stalk t hη x,
    LineParameter.RationalFractions.fraction_field]
  change Cycles.Functoriality.FunctionFields.Construction.genericFieldMap t hη (LineParameter.RationalFractions.ratio 1 0 1) = _
  rw [LineParameter.RationalFractions.ratio_reverse 1 1 0, map_inv₀]
  rfl

omit [IsIntegral Z] in
theorem inverseGerm_nonunit (x : Z) (hx : t x ∉ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) :
    ¬ IsUnit (inverseGerm t x hx) := by
  rw [inverseGerm, isUnit_map_iff (t.stalkMap x).hom, FormStalkComparison.ProjectiveFractionUnits.fraction]
  exact hx

theorem shifted_inverse (x : Z) (hx : t x ∉ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) (a : ℂ) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    ∃ u : Z.presheaf.stalk x, algebraMap (Z.presheaf.stalk x) Z.functionField u =
      (LineParameter.pullback t hη - algebraMap ℂ Z.functionField a)⁻¹ := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  let := FunctionDivisor.stalkScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) x
  let := FunctionDivisor.stalkScalarTower (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) x
  have hg : LineParameter.pullback t hη ≠ 0 := by
    intro he
    have ht := ParameterGerms.Pencil.transcendental t hη
    rw [he] at ht
    exact ht isAlgebraic_zero
  have h := NonunitParameterShift.inverse (Z.presheaf.stalk x) Z.functionField
    (LineParameter.pullback t hη) hg (algebraMap ℂ (Z.presheaf.stalk x) a)
    (inverseGerm t x hx) (inverseGerm_field t hη x hx) (inverseGerm_nonunit t x hx)
  rwa [← IsScalarTower.algebraMap_apply] at h

theorem positive_zero [AlgebraicGeometry.IsNoetherian Z]
    (x : Z) (hx : t x ∉ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) (a : ℂ) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z
      (LineParameter.pullback t hη - algebraMap ℂ Z.functionField a)) x = 0 := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  obtain ⟨u, hu⟩ := shifted_inverse t hη x hx a
  by_contra hn
  exact InverseDivisorSupport.positive_avoids Z x u _ hu x
    (Finsupp.mem_support_iff.mpr hn) (specializes_refl x)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterInfinity
