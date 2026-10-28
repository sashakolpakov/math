import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompactHorizontalFamilyFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FamilyChart

/-! # Source Endpoint Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceEndpointFiber

noncomputable section

/-! Every point of a good scalar fiber of the source family lies
on its native closed section, whose projection is the identity on X. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Polynomial

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)

theorem range : Set.range (Projective.FamilyOnSource.Family.specialization X A a ha) =
    CompactHorizontalFamilyFiber.Family.parameter X A ⁻¹' {Affine.ParameterFiber.point ℂ a} := by
  let e := Spec.map (CommRingCat.ofHom (Polynomial.MatrixPath.evaluation A a ha))
  let c := IsLocalRing.closedPoint ℂ
  have hr := Open.SupportClosure.Pullback.range (Projective.FamilyOnSource.Family.specialization X A a ha)
    X.structureMap (Projective.FamilySections.Family.parameter X A) e
    (Projective.FamilyIs.FamilyFibers.source X A a ha)
  have he : Parameter.Polynomial.IntegralProduct.toLine A (e c) = Affine.ParameterFiber.point ℂ a :=
    (congrArg (fun g : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Spec (.of ℂ[X]) => g c)
      (Parameter.FamilyChart.Family.evaluation_toLine A a ha)).trans
      (Affine.ParameterFiber.point_spec ℂ a)
  have her : Set.range e = {e c} := by
    ext q
    constructor
    · rintro ⟨b, rfl⟩
      exact congrArg e (Subsingleton.elim b c)
    · rintro rfl
      exact ⟨c, rfl⟩
  rw [hr, her]
  ext x
  change Projective.FamilySections.Family.parameter X A x = e c ↔
    Parameter.Polynomial.IntegralProduct.toLine A (Projective.FamilySections.Family.parameter X A x) =
      Affine.ParameterFiber.point ℂ a
  constructor
  · intro hx
    exact (congrArg (Parameter.Polynomial.IntegralProduct.toLine A) hx).trans he
  · intro hx
    exact (Parameter.Polynomial.IntegralProduct.toLine A).isEmbedding.injective (hx.trans he.symm)

theorem point (y : Projective.FamilyOnSource.Family.space X A)
    (hy : CompactHorizontalFamilyFiber.Family.parameter X A y = Affine.ParameterFiber.point ℂ a) :
    Projective.FamilyOnSource.Family.specialization X A a ha (Projective.FamilyOnSource.Family.toSource X A y) = y := by
  have hm : y ∈ Set.range (Projective.FamilyOnSource.Family.specialization X A a ha) := by
    rw [SourceEndpointFiber.range]
    exact hy
  obtain ⟨x, rfl⟩ := hm
  have hr := congrArg (fun f : X.carrier ⟶ X.carrier => f x)
    (Projective.FamilyOnSource.Family.specialization_source X A a ha)
  exact congrArg (Projective.FamilyOnSource.Family.specialization X A a ha) hr

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceEndpointFiber
