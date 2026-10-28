import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms

/-! # Pair Linear Constraints -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PairLinearConstraints

noncomputable section

/-! Distinct projective points impose a proper linear constraint
when one extends a partially chosen system of projection coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (p q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier)
  (hp : p ≫ X.structureMap = 𝟙 _) (hq : q ≫ X.structureMap = 𝟙 _)

theorem separating_form (hne : p (IsLocalRing.closedPoint ℂ) ≠ q (IsLocalRing.closedPoint ℂ)) :
    ∃ a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1,
      PointFiberLinearForms.value X p hp a = 0 ∧ PointFiberLinearForms.value X q hq a ≠ 0 := by
  have hpx : IsClosed ({p (IsLocalRing.closedPoint ℂ)} : Set X.carrier) :=
    ((pointEquivClosedPoint X.structureMap) ⟨p, hp⟩).property
  have hqx : IsClosed ({q (IsLocalRing.closedPoint ℂ)} : Set X.carrier) :=
    ((pointEquivClosedPoint X.structureMap) ⟨q, hq⟩).property
  have hpe : IsClosed ({X.embedding (p (IsLocalRing.closedPoint ℂ))} : Set _) := by
    simpa only [Set.image_singleton] using X.embedding.isClosedEmbedding.isClosedMap _ hpx
  have hqe : IsClosed ({X.embedding (q (IsLocalRing.closedPoint ℂ))} : Set _) := by
    simpa only [Set.image_singleton] using X.embedding.isClosedEmbedding.isClosedMap _ hqx
  obtain ⟨a, ha, hb⟩ := Closed.PointLinearSeparation.points X.ambientDimension
    (X.embedding (p (IsLocalRing.closedPoint ℂ))) (X.embedding (q (IsLocalRing.closedPoint ℂ)))
    hpe hqe (fun he => hne (X.embedding.isClosedEmbedding.injective he))
  exact ⟨a, (PointFiberLinearForms.value_zero X p hp a).mpr ha, fun h => hb ((PointFiberLinearForms.value_zero X q hq a).mp h)⟩

def determinant (s : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1 →ₗ[ℂ] ℂ :=
  PointFiberLinearForms.value X p hp s • PointFiberLinearForms.value X q hq - PointFiberLinearForms.value X q hq s • PointFiberLinearForms.value X p hp

theorem determinant_apply (s a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    determinant X p q hp hq s a =
      PointFiberLinearForms.value X p hp s * PointFiberLinearForms.value X q hq a - PointFiberLinearForms.value X q hq s * PointFiberLinearForms.value X p hp a := rfl

theorem determinant_nonzero
    (hne : p (IsLocalRing.closedPoint ℂ) ≠ q (IsLocalRing.closedPoint ℂ))
    (s : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hs : PointFiberLinearForms.value X p hp s ≠ 0 ∨ PointFiberLinearForms.value X q hq s ≠ 0) :
    ∃ a, determinant X p q hp hq s a ≠ 0 := by
  rcases hs with hs | hs
  · obtain ⟨a, ha, hb⟩ := separating_form X p q hp hq hne
    refine ⟨a, ?_⟩
    rw [determinant_apply, ha, mul_zero, sub_zero]
    exact mul_ne_zero hs hb
  · obtain ⟨a, ha, hb⟩ := separating_form X q p hq hp hne.symm
    refine ⟨a, ?_⟩
    rw [determinant_apply, ha, mul_zero, zero_sub, neg_ne_zero]
    exact mul_ne_zero hs hb

theorem kernel_ne_top
    (hne : p (IsLocalRing.closedPoint ℂ) ≠ q (IsLocalRing.closedPoint ℂ))
    (s : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hs : PointFiberLinearForms.value X p hp s ≠ 0 ∨ PointFiberLinearForms.value X q hq s ≠ 0) :
    LinearMap.ker (determinant X p q hp hq s) ≠ ⊤ := by
  obtain ⟨a, ha⟩ := determinant_nonzero X p q hp hq hne s hs
  intro he
  have hm : a ∈ LinearMap.ker (determinant X p q hp hq s) := by rw [he]; trivial
  exact ha hm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PairLinearConstraints
