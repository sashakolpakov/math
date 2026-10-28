import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PointLinearSeparation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FormStalkComparison
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointJetCoordinates

/-! # Point Fiber Linear Forms -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms

noncomputable section

/-! Linear equations for the fiber through a chosen rational point,
and properness of their avoidance constraints at another closed point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier) (hp : p ≫ X.structureMap = 𝟙 _)

attribute [local instance] PointJetCoordinates.scalar

def value : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] ℂ :=
  (LinearMap.fst ℂ ℂ _).comp (PointJetCoordinates.map X p hp)

theorem value_zero (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    value X p hp a = 0 ↔
      a.val ∈ (X.embedding (p (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal :=
  FormStalkComparison.ProjectiveFractionUnits.form X.ambientDimension (PointJetCoordinates.coordinate X p)
    X.embedding p (PointJetCoordinates.over X p hp)
    (PointJetCoordinates.coordinate_mem X p) a

def cross (s : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 :=
  value X p hp s • LinearMap.id - (value X p hp).smulRight s

theorem cross_apply (s a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    cross X p hp s a = value X p hp s • a - value X p hp a • s := rfl

theorem cross_vanishes (s a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    (cross X p hp s a).val ∈
      (X.embedding (p (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal := by
  apply (value_zero X p hp _).mp
  rw [cross_apply, map_sub, map_smul, map_smul]
  change value X p hp s * value X p hp a - value X p hp a * value X p hp s = 0
  ring

theorem constraint_ne_top (s : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hs : value X p hp s ≠ 0) (y : X.carrier) (hy : IsClosed ({y} : Set _))
    (hne : y ≠ p (IsLocalRing.closedPoint ℂ)) :
    (ConstrainedLinearForms.pointSubmodule X.ambientDimension (X.embedding y)).comap
      (cross X p hp s) ≠ ⊤ := by
  have hx : IsClosed ({p (IsLocalRing.closedPoint ℂ)} : Set X.carrier) :=
    ((pointEquivClosedPoint X.structureMap) ⟨p, hp⟩).property
  have hxe : IsClosed ({X.embedding (p (IsLocalRing.closedPoint ℂ))} : Set _) := by
    simpa only [Set.image_singleton] using X.embedding.isClosedEmbedding.isClosedMap _ hx
  have hye : IsClosed ({X.embedding y} : Set _) := by
    simpa only [Set.image_singleton] using X.embedding.isClosedEmbedding.isClosedMap _ hy
  obtain ⟨a, hax, hay⟩ := Closed.PointLinearSeparation.points X.ambientDimension
    (X.embedding (p (IsLocalRing.closedPoint ℂ))) (X.embedding y) hxe hye
    (fun he => hne (X.embedding.isClosedEmbedding.injective he).symm)
  have ha : value X p hp a = 0 := (value_zero X p hp a).mpr hax
  intro he
  have hm : a ∈ (ConstrainedLinearForms.pointSubmodule X.ambientDimension
      (X.embedding y)).comap (cross X p hp s) := by rw [he]; trivial
  change cross X p hp s a ∈ ConstrainedLinearForms.pointSubmodule _ _ at hm
  rw [cross_apply, ha, zero_smul, sub_zero,
    (ConstrainedLinearForms.pointSubmodule _ _).smul_mem_iff hs] at hm
  exact hay hm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms
