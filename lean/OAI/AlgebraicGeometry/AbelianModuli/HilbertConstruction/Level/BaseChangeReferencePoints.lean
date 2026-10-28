import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GeometricPointDiagram

/-! # Base Change Reference Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The represented torsion isomorphism and the functorial ordered level
have the same underlying points in the original abelian scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S T : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) (f : T ⟶ S)

theorem Level.BaseChangeReferencePoints.constantFullLevelBaseChangeYonedaIso_point (U : Over T)
    (q : U ⟶ (Over.pullback f).obj (Level.Scheme.constantFullLevelScheme g N S)) :
    (Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N f).hom.app (.op U) q =
      (Level.Scheme.constantFullLevelRepresentable g N S).homEquiv
        (GroupBaseChangePoints.groupBaseChangePointsEquiv (Level.Scheme.constantFullLevelScheme g N S) f U q) := rfl

variable (l : (A.pullback f).FullLevel N)

theorem Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv_original_point (U : Over T)
    (q : U ⟶ (Over.pullback f).obj (Level.Scheme.constantFullLevelScheme g N S)) :
    q.left ≫ (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N f l).hom.hom.hom.left ≫
      pullback.fst (A.torsionScheme N).hom f ≫ (A.torsionInclusion N).left =
        (l.hom.app (.op U)
          ((Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N f).hom.app (.op U) q)).val.left ≫
            pullback.fst A.scheme.hom f := by
  have h := Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv_point A N f l U q
  have h' := congrArg (fun z : (A.pullback f).torsionPoints N U =>
    (A.torsionBaseChangeEquiv f U N z).val.left) h
  change (A.torsionBaseChangeEquiv f U N
      ((A.torsionBaseChangeEquiv f U N).symm
        (A.torsionSchemePointsEquiv N ((Over.map f).obj U)
          (GroupBaseChangePoints.groupBaseChangePointsEquiv (A.torsionScheme N) f U
            (q ≫ (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N f l).hom.hom.hom))))).val.left = _ at h'
  rw [MulEquiv.apply_symm_apply] at h'
  change ((q.left ≫ (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N f l).hom.hom.hom.left) ≫
      pullback.fst (A.torsionScheme N).hom f) ≫ (A.torsionInclusion N).left =
        (l.hom.app (.op U)
          ((Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N f).hom.app (.op U) q)).val.left ≫
            pullback.fst A.scheme.hom f at h'
  simpa only [Category.assoc] using h'

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
