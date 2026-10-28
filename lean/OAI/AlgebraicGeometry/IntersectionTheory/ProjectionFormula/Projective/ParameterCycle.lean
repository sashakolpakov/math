import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PositiveParameterFiber

/-! # Parameter Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterCycle

noncomputable section

/-! Positive fibers of projective parameters as finite point-cycles,
with naturality for commuting open immersions and native parameter maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

variable {Z : Scheme} [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]

def cycle (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
    (hη : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)) (a : ℂ) : Z →₀ ℚ :=
  letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (t ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)
  PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z
    (LineParameter.pullback t hη - algebraMap ℂ Z.functionField a))

theorem congr {s t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1} (h : s = t)
    (hs : s (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (ht : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)) (a : ℂ) :
    cycle s hs a = cycle t ht a := by
  subst t
  rfl

variable {Y : Scheme} [IsIntegral Y] [AlgebraicGeometry.IsNoetherian Y]
  (i : Y ⟶ Z) [IsOpenImmersion i]
  (s : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
  (hs : s (genericPoint Y) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
  (ht : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

theorem pushforward (h : s = i ≫ t) (a : ℂ)
    (hcover : ∀ z : Z, t z = ParameterFiber.point a → z ∈ Set.range i) :
    CyclePushforward.pointPushforward i (cycle s hs a) = cycle t ht a := by
  subst s
  exact Open.PositiveParameterFiber.pushforward i t ht a hcover

theorem compose {X : Scheme} (f : Z ⟶ X) (h : s = i ≫ t) (a : ℂ)
    (hcover : ∀ z : Z, t z = ParameterFiber.point a → z ∈ Set.range i) :
    CyclePushforward.pointPushforward (i ≫ f) (cycle s hs a) = CyclePushforward.pointPushforward f (cycle t ht a) := by
  rw [CyclePushforward.pointPushforward_comp, LinearMap.comp_apply, pushforward i s t hs ht h a hcover]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterCycle
