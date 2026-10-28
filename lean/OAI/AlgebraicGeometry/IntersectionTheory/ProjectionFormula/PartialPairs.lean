import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PartialLinear
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiberEquations

/-! # Partial Pairs -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PartialPairs

noncomputable section

/-! A nonzero determinant of two chosen coordinates separates the
images of two closed points under the actual partial projection. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PartialLinear.Projection

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
  (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)

theorem determinant_zero (p q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier)
    (hp : p ≫ X.structureMap = 𝟙 _) (hq : q ≫ X.structureMap = 𝟙 _)
    (hpx : p (IsLocalRing.closedPoint ℂ) ∈ PartialLinear.Projection.domain X k L)
    (hqx : q (IsLocalRing.closedPoint ℂ) ∈ PartialLinear.Projection.domain X k L)
    (he : PartialLinear.Projection.map X k L ⟨p (IsLocalRing.closedPoint ℂ), hpx⟩ =
      PartialLinear.Projection.map X k L ⟨q (IsLocalRing.closedPoint ℂ), hqx⟩)
    (i a : Fin (k + 1)) :
    PairLinearConstraints.determinant X p q hp hq (L i) (L a) = 0 := by
  let e := Projection.FiberEquations.equation X k L p hp i a
  have hv : e.val ∈ (PartialLinear.Projection.map X k L ⟨p (IsLocalRing.closedPoint ℂ), hpx⟩).asHomogeneousIdeal := by
    apply (PartialLinear.Projection.homogeneous_mem X k L _ e).mpr
    rw [Projection.FiberEquations.equation_pull]
    exact PointFiberLinearForms.cross_vanishes X p hp (L i) (L a)
  have hvq : e.val ∈ (PartialLinear.Projection.map X k L ⟨q (IsLocalRing.closedPoint ℂ), hqx⟩).asHomogeneousIdeal := he ▸ hv
  have hw := (PartialLinear.Projection.homogeneous_mem X k L _ e).mp hvq
  rw [Projection.FiberEquations.equation_pull] at hw
  have hz := (PointFiberLinearForms.value_zero X q hq (PointFiberLinearForms.cross X p hp (L i) (L a))).mpr hw
  rw [PointFiberLinearForms.cross_apply, map_sub, map_smul, map_smul] at hz
  change PointFiberLinearForms.value X p hp (L i) * PointFiberLinearForms.value X q hq (L a) -
    PointFiberLinearForms.value X p hp (L a) * PointFiberLinearForms.value X q hq (L i) = 0 at hz
  rw [PairLinearConstraints.determinant_apply, mul_comm (PointFiberLinearForms.value X q hq (L i))]
  exact hz

theorem domain_cons (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    PartialLinear.Projection.domain X k L ≤ PartialLinear.Projection.domain X (k + 1) (Fin.cons a L) := by
  intro x hx
  obtain ⟨i, hi⟩ := (PartialLinear.Projection.mem_domain X k L x).mp hx
  exact (PartialLinear.Projection.mem_domain X (k + 1) (Fin.cons a L) x).mpr ⟨i.succ, hi⟩

theorem extension_separates (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (p q : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier)
    (hp : p ≫ X.structureMap = 𝟙 _) (hq : q ≫ X.structureMap = 𝟙 _)
    (hpx : p (IsLocalRing.closedPoint ℂ) ∈ PartialLinear.Projection.domain X k L)
    (hqx : q (IsLocalRing.closedPoint ℂ) ∈ PartialLinear.Projection.domain X k L)
    (i : Fin (k + 1))
    (hd : PairLinearConstraints.determinant X p q hp hq (L i) a ≠ 0) :
    PartialLinear.Projection.map X (k + 1) (Fin.cons a L)
        ⟨p (IsLocalRing.closedPoint ℂ), domain_cons X k L a hpx⟩ ≠
      PartialLinear.Projection.map X (k + 1) (Fin.cons a L)
        ⟨q (IsLocalRing.closedPoint ℂ), domain_cons X k L a hqx⟩ := by
  intro he
  exact hd (determinant_zero X (k + 1) (Fin.cons a L) p q hp hq _ _ he i.succ 0)

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PartialPairs
