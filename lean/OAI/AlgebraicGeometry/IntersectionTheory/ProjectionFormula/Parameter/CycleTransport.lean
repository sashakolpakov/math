import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PositiveParameterFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyFiber

/-! # Cycle Transport -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.CycleTransport

noncomputable section

/-! Small transport lemmas keep endpoint comparisons in native
point-cycle coordinates without expanding the reduced closure models. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem horizontal {Y Z : Scheme} [IsIntegral Y] [IsIntegral Z]
    (i : Y ⟶ Z) [IsOpenImmersion i] (s : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
    (h : s = i ≫ t) (ht : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)) :
    s (genericPoint Y) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) := by
  subst s
  exact Projective.ParameterRestriction.generic i t ht

theorem family_formula {X Z : Scheme} [AlgebraicGeometry.IsNoetherian Z]
    (q : Z ⟶ X) (C : IrreducibleCloseds Z) (t : Z ⟶ Spec (.of ℂ[X]))
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)) (a : ℂ) :
    CyclePushforward.pointPushforward q (HorizontalFamilyFiber.Family.cycle Z C t hη a) =
    CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ q)
      (Projective.ParameterCycle.cycle ((CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ t) ≫ Projective.FamilyIs.MatrixParameterOpen.affine) hη a) := by
  rw [CyclePushforward.pointPushforward_comp, LinearMap.comp_apply]
  rfl

theorem proper_formula (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {Y Z : Scheme}
    [IsIntegral Y] [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Z]
    (f : Z ⟶ X.carrier) (i : Y ⟶ Z) [IsOpenImmersion i] (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
    (ht : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (j : Y ⟶ X.carrier) (s : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
    (hs : s (genericPoint Y) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (hj : i ≫ f = j) (hp : i ≫ t = s) (p : ℕ) (a : ℂ) :
    Open.PositiveParameterFiber.ProperPencil.fiber X f i t ht p a =
      CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward j (Projective.ParameterCycle.cycle s hs a)) := by
  change CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (i ≫ f)
    (Projective.ParameterCycle.cycle (i ≫ t) (Projective.ParameterRestriction.generic i t ht) a)) = _
  rw [hj, Projective.ParameterCycle.congr hp _ hs a]

theorem compose_congr {Y Z X : Scheme} [IsIntegral Y] [IsIntegral Z]
    [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Z]
    (i : Y ⟶ Z) [IsOpenImmersion i] (s : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) (t : Z ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)
    (hs : s (genericPoint Y) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (ht : t (genericPoint Z) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (f : Z ⟶ X) (j : Y ⟶ X) (hj : i ≫ f = j) (hp : s = i ≫ t) (a : ℂ)
    (hcover : ∀ z : Z, t z = Projective.ParameterFiber.point a → z ∈ Set.range i) :
    CyclePushforward.pointPushforward j (Projective.ParameterCycle.cycle s hs a) =
      CyclePushforward.pointPushforward f (Projective.ParameterCycle.cycle t ht a) := by
  rw [← hj]
  exact Projective.ParameterCycle.compose i s t hs ht f hp a hcover

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.CycleTransport
