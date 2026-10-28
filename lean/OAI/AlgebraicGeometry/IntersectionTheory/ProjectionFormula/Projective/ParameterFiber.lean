import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterInfinity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterComparison

/-! # Parameter Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterFiber

noncomputable section

/-! The positive divisor of a dominant projective-line parameter
is supported on the actual scalar fiber, including on singular schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Polynomial

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIs.MatrixParameterOpen

theorem range_affine : Set.range FamilyIs.MatrixParameterOpen.affine = (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0 : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)) := by
  let e := Scheme.Spec.mapIso FamilyIs.MatrixParameterOpen.chartEquiv.toRingEquiv.toCommRingCatIso.op
  change Set.range ((Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0).ι ∘
    (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec 1 0).inv ∘ e.hom) = _
  rw [Set.range_comp, Set.range_comp, e.hom.surjective.range_eq, Set.image_univ,
    (Foundations.Scheme.ProjectiveChart.projectiveCoordinateIsoSpec 1 0).inv.surjective.range_eq, Set.image_univ]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

def point (a : ℂ) : Foundations.Scheme.ProjectiveSpace.projectiveSpace 1 := FamilyIs.MatrixParameterOpen.affine (Affine.ParameterFiber.point ℂ a)

theorem point_mem (a : ℂ) : point a ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0 :=
  Affine.ProjectiveParameter.contained _

def shift (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) (hx : x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) (a : ℂ) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1).presheaf.stalk x :=
  letI := Stalk.PointAlgebra.scalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) x
  PointJets.StalkFractions.fraction 1 x
    (LineParameter.RationalFractions.coordinate 1 1)
    (LineParameter.RationalFractions.coordinate 1 0) hx -
      algebraMap ℂ ((Foundations.Scheme.ProjectiveSpace.projectiveSpace 1).presheaf.stalk x) a

theorem map_shift {Z : Scheme} (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
    (x : Z) (hx : t x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) (a : ℂ) :
    t.stalkMap x (shift (t x) hx a) = ParameterGerms.shiftedGerm t x hx a := by
  let := Stalk.PointAlgebra.scalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) (t x)
  let := Stalk.PointAlgebra.scalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) x
  rw [shift, map_sub, ParameterGerms.shiftedGerm]
  exact congrArg (fun c => ParameterGerms.finiteGerm t x hx - c)
    ((Stalk.ScalarMaps.stalk t (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) x).commutes a)

theorem shift_isUnit (x : Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) (hx : x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) (a : ℂ) :
    IsUnit (shift x hx a) ↔ x ≠ point a := by
  obtain ⟨y, rfl⟩ := (Set.ext_iff.mp range_affine x).mpr hx
  rw [← isUnit_map_iff (FamilyIs.MatrixParameterOpen.affine.stalkMap y).hom, map_shift, Affine.ParameterComparison.affine_shift,
    Affine.ParameterFiber.toStalk_unit, not_congr (Affine.ParameterFiber.mem_iff ℂ y a)]
  exact (not_congr FamilyIs.MatrixParameterOpen.affine.isOpenEmbedding.injective.eq_iff).symm

theorem shiftedGerm_isUnit {Z : Scheme} (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
    (x : Z) (hx : t x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) (a : ℂ) :
    IsUnit (ParameterGerms.shiftedGerm t x hx a) ↔ t x ≠ point a := by
  rw [← map_shift, isUnit_map_iff (t.stalkMap x).hom, shift_isUnit]

variable {Z : Scheme} [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
  (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) (hη : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

theorem positive_zero (a : ℂ) (x : Z) (hx : t x ≠ point a) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z
      (LineParameter.pullback t hη - algebraMap ℂ Z.functionField a)) x = 0 := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  by_cases hf : t x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0
  · rw [← ParameterGerms.shiftedGerm_field t hη x hf a,
      PositiveCycle.positivePart_apply, Affine.DivisorNorm.rationalPrincipalDivisor_apply,
      UnitDivisorSupport.order_zero Z x x (specializes_refl x) _
        ((shiftedGerm_isUnit t x hf a).mpr hx), Int.cast_zero, max_self]
  · exact ParameterInfinity.positive_zero t hη x hf a

theorem positive_support (a : ℂ) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    ∀ x ∈ (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z
      (LineParameter.pullback t hη - algebraMap ℂ Z.functionField a))).support,
      t x = point a := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  intro x hx
  by_contra hn
  exact Finsupp.mem_support_iff.mp hx (positive_zero t hη a x hn)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterFiber
