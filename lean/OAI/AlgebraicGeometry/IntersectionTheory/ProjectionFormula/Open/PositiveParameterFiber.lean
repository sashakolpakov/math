import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterGerms

/-! # Positive Parameter Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PositiveParameterFiber

noncomputable section

section

/-! An open chart covering a scalar fiber carries its entire positive
parameter divisor. Its pushforward is the original finite point-cycle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

variable {Y Z : Scheme} [IsIntegral Y] [IsIntegral Z]
  [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Z]
  (i : Y ⟶ Z) [IsOpenImmersion i] (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
  (hη : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

theorem pushforward (a : ℂ)
    (hcover : ∀ z : Z, t z = Projective.ParameterFiber.point a → z ∈ Set.range i) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    CyclePushforward.pointPushforward i (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Y
      (Projective.LineParameter.pullback (i ≫ t) (Projective.ParameterRestriction.generic i t hη) -
        algebraMap ℂ Y.functionField a))) =
    PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z
      (Projective.LineParameter.pullback t hη - algebraMap ℂ Z.functionField a)) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  ext z
  by_cases hz : z ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hz
    rw [PushforwardFiber.pointPushforward_uniqueFiber i y (i y) rfl
      (fun b hb => i.isOpenEmbedding.injective hb),
      Principal.ClosedSectionCycle.residueDegree_immersion, Nat.cast_one, mul_one]
    exact Projective.ParameterRestriction.positive i t hη a y
  · rw [PushforwardFiber.pointPushforward_apply_eq_zero i _ z
      (fun y _ he => hz ⟨y, he⟩)]
    exact (Projective.ParameterFiber.positive_zero t hη a z (fun he => hz (hcover z he))).symm

theorem compose {X : Scheme} (f : Z ⟶ X) (a : ℂ)
    (hcover : ∀ z : Z, t z = Projective.ParameterFiber.point a → z ∈ Set.range i) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
    CyclePushforward.pointPushforward (i ≫ f) (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Y
      (Projective.LineParameter.pullback (i ≫ t) (Projective.ParameterRestriction.generic i t hη) -
        algebraMap ℂ Y.functionField a))) =
    CyclePushforward.pointPushforward f (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z
      (Projective.LineParameter.pullback t hη - algebraMap ℂ Z.functionField a))) := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  rw [CyclePushforward.pointPushforward_comp, LinearMap.comp_apply, pushforward i t hη a hcover]

end

/-! The scalar fibers of a proper projective parameter may be computed
on any open scheme covering them, while retaining rational equivalence. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace ProperPencil

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {Y Z : Scheme} [IsIntegral Y] [IsIntegral Z]
  [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Z]
  (f : Z ⟶ X.carrier) [IsProper f] (i : Y ⟶ Z) [IsOpenImmersion i]
  (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) (hη : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

def fiber (p : ℕ) (a : ℂ) : X.RationalDimensionCycle p :=
  letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra ((i ≫ t) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (i ≫ f) (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Y
    (Projective.LineParameter.pullback (i ≫ t) (Projective.ParameterRestriction.generic i t hη) -
      algebraMap ℂ Y.functionField a))))

omit [IsProper f] in
theorem fiber_eq (hbase : t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1 = f ≫ X.structureMap)
    (p : ℕ) (a : ℂ)
    (hcover : ∀ z : Z, t z = Projective.ParameterFiber.point a → z ∈ Set.range i) :
    fiber X f i t hη p a = NormalizedRationalPencil.Proper.fiber X f p
      (Projective.LineParameter.pullback t hη) a := by
  have he := compose i t hη f a hcover
  rw [hbase] at he
  exact congrArg (CyclePushforward.degreeComponent X p) he

theorem rationallyEquivalent (hbase : t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1 = f ≫ X.structureMap)
    (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ X.structureMap) + p = m + 1) (a b : ℂ)
    (ha : ∀ z : Z, t z = Projective.ParameterFiber.point a → z ∈ Set.range i)
    (hb : ∀ z : Z, t z = Projective.ParameterFiber.point b → z ∈ Set.range i) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (fiber X f i t hη p a) (fiber X f i t hη p b) := by
  rw [fiber_eq X f i t hη hbase p a ha, fiber_eq X f i t hη hbase p b hb]
  exact Projective.ParameterGerms.Pencil.rationallyEquivalent t hη X f hbase m p hd a b

end ProperPencil

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PositiveParameterFiber
