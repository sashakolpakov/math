import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.FamilyChart
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyRegularity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ParameterFiber

/-! # Endpoint Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.EndpointFiber

noncomputable section

/-! A marked projective matrix-family section is the entire scalar
fiber of its actual affine parameter, at the level of scheme points. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Polynomial

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
  (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)

theorem range : Set.range (MatrixFamily.Family.specialization A a ha) =
    FamilyRegularity.IntegralFamilySupport.parameterLine A ⁻¹' {Affine.ParameterFiber.point ℂ a} := by
  let h := FamilyIs.FamilyFibers.ambient A a ha
  have hr : Set.range (MatrixFamily.Family.specialization A a ha) =
      Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n ⁻¹'
        Set.range (Spec.map (CommRingCat.ofHom (Polynomial.MatrixPath.evaluation A a ha))) := by
    rw [← h.isoPullback_hom_fst]
    change Set.range (pullback.fst (Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n)
      (Spec.map (CommRingCat.ofHom (Polynomial.MatrixPath.evaluation A a ha))) ∘ h.isoPullback.hom) = _
    rw [Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ, Scheme.Pullback.range_fst]
  let e := Spec.map (CommRingCat.ofHom (Polynomial.MatrixPath.evaluation A a ha))
  let c := IsLocalRing.closedPoint ℂ
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
  change Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n x = e c ↔
    Parameter.Polynomial.IntegralProduct.toLine A (Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) n x) =
      Affine.ParameterFiber.point ℂ a
  constructor
  · intro hx
    exact (congrArg (Parameter.Polynomial.IntegralProduct.toLine A) hx).trans he
  · intro hx
    exact (Parameter.Polynomial.IntegralProduct.toLine A).isEmbedding.injective (hx.trans he.symm)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.EndpointFiber
