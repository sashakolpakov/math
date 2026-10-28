import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Coincidence

/-! # Coincidence Extension -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoincidenceExtension

noncomputable section

/-! Extending a projection by a form with nonzero pair determinant
removes that pair from the closed coincidence locus. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Coincidence

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
  (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (u v : T ⟶ X.toOver)

theorem first_value (x : Projection.Coincidence.domain X k L u v) :
    (Projection.Coincidence.first X k L u v).left x = PartialLinear.Projection.map X k L
      ⟨u.left x.val, x.property.1⟩ := by
  change PartialLinear.Projection.map X k L
    (u.left.resLE (PartialLinear.Projection.domain X k L) (Projection.Coincidence.domain X k L u v) inf_le_left x) = _
  congr 1
  apply Subtype.ext
  exact Scheme.Hom.coe_resLE_apply u.left inf_le_left x

theorem second_value (x : Projection.Coincidence.domain X k L u v) :
    (Projection.Coincidence.second X k L u v).left x = PartialLinear.Projection.map X k L
      ⟨v.left x.val, x.property.2⟩ := by
  change PartialLinear.Projection.map X k L
    (v.left.resLE (PartialLinear.Projection.domain X k L) (Projection.Coincidence.domain X k L u v) inf_le_right x) = _
  congr 1
  apply Subtype.ext
  exact Scheme.Hom.coe_resLE_apply v.left inf_le_right x

theorem domain_cons (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    Projection.Coincidence.domain X k L u v ≤ Projection.Coincidence.domain X (k + 1) (Fin.cons a L) u v := by
  intro x hx
  exact ⟨PartialPairs.Projection.domain_cons X k L a hx.1,
    PartialPairs.Projection.domain_cons X k L a hx.2⟩

theorem point_over (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ T.left) (hp : p ≫ T.hom = 𝟙 _) :
    (p ≫ u.left) ≫ X.structureMap = 𝟙 _ := by
  rw [Category.assoc]
  exact (congrArg (fun f : T.left ⟶ Foundations.Scheme.ProjectiveSpace.complexBase => p ≫ f) u.w).trans hp

theorem excludes (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ T.left) (hp : p ≫ T.hom = 𝟙 _)
    (hx : p (IsLocalRing.closedPoint ℂ) ∈ Projection.Coincidence.domain X k L u v)
    (i : Fin (k + 1))
    (hd : PairLinearConstraints.determinant X (p ≫ u.left) (p ≫ v.left)
      (point_over X u p hp) (point_over X v p hp) (L i) a ≠ 0) :
    p (IsLocalRing.closedPoint ℂ) ∉ Projection.Coincidence.locus X (k + 1) (Fin.cons a L) u v := by
  let x : Projection.Coincidence.domain X (k + 1) (Fin.cons a L) u v :=
    ⟨p (IsLocalRing.closedPoint ℂ), domain_cons X k L u v a hx⟩
  apply Projection.Coincidence.not_mem_of_ne X (k + 1) (Fin.cons a L) u v x
  rw [first_value, second_value]
  exact PartialPairs.Projection.extension_separates X k L a
    (p ≫ u.left) (p ≫ v.left) (point_over X u p hp) (point_over X v p hp)
    hx.1 hx.2 i hd

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoincidenceExtension
