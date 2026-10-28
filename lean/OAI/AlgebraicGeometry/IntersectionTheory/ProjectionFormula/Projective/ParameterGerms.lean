import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.CoordinateTranscendence
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PencilFiberComparison

/-! # Parameter Germs -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterGerms

noncomputable section

section

/-! A dominant morphism to the actual projective line supplies the
rational parameter and regularity needed by the proper-pencil theorem.
Its scalar fibers give rationally equivalent cycles on the target. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Pencil

variable {Z : Scheme} [IsIntegral Z] (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
  (hη : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

theorem transcendental :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    Transcendental ℂ (LineParameter.pullback t hη) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  let φ := Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom t hη (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  have ht := CoordinateTranscendence.transcendental 1 0 1 (by decide)
  intro h
  exact ht ((isAlgebraic_algHom_iff φ φ.injective).mp h)

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [AlgebraicGeometry.IsNoetherian Z]
  (f : Z ⟶ X.carrier) [IsProper f]

theorem rationallyEquivalent (hbase : t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1 = f ≫ X.structureMap)
    (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap) + p = m + 1) (a b : ℂ) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p
      (NormalizedRationalPencil.Proper.fiber X f p (LineParameter.pullback t hη) a)
      (NormalizedRationalPencil.Proper.fiber X f p (LineParameter.pullback t hη) b) := by
  have ht := transcendental t hη
  rw [hbase] at ht
  exact Proper.PencilFiberComparison.rationallyEquivalent X f m p hd
    (LineParameter.pullback t hη)
    (LineParameter.pullback_charts t hη) ht a b

end Pencil

end

/-! On the finite coordinate chart, the projective parameter and
each of its scalar translates have explicit regular representatives
in the actual source stalks. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {Z : Scheme} [IsIntegral Z] (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
  (hη : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

def finiteGerm (x : Z) (hx : t x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) : Z.presheaf.stalk x :=
  t.stalkMap x (PointJets.StalkFractions.fraction 1 (t x)
    (LineParameter.RationalFractions.coordinate 1 1)
    (LineParameter.RationalFractions.coordinate 1 0) hx)

theorem finiteGerm_field (x : Z) (hx : t x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) :
    algebraMap (Z.presheaf.stalk x) Z.functionField (finiteGerm t x hx) =
      LineParameter.pullback t hη := by
  rw [finiteGerm, ← Divisor.DivisorRestriction.genericFieldMap_stalk t hη x,
    LineParameter.RationalFractions.fraction_field]
  rfl

def shiftedGerm (x : Z) (hx : t x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) (a : ℂ) : Z.presheaf.stalk x :=
  letI := Stalk.PointAlgebra.scalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) x
  finiteGerm t x hx - algebraMap ℂ (Z.presheaf.stalk x) a

theorem shiftedGerm_field (x : Z) (hx : t x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) (a : ℂ) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    algebraMap (Z.presheaf.stalk x) Z.functionField (shiftedGerm t x hx a) =
      LineParameter.pullback t hη - algebraMap ℂ Z.functionField a := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  let := Stalk.PointAlgebra.scalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) x
  let := FunctionDivisor.stalkScalarTower (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1) x
  rw [shiftedGerm, map_sub, finiteGerm_field t hη, ← IsScalarTower.algebraMap_apply]

include hη in
theorem shiftedGerm_ne_zero (x : Z) (hx : t x ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen 1 0) (a : ℂ) :
    shiftedGerm t x hx a ≠ 0 := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  intro h
  have he := shiftedGerm_field t hη x hx a
  rw [h, map_zero] at he
  have hc : LineParameter.pullback t hη = algebraMap ℂ Z.functionField a :=
    sub_eq_zero.mp he.symm
  have ht := Pencil.transcendental t hη
  rw [hc] at ht
  exact ht (isAlgebraic_algebraMap a)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterGerms
