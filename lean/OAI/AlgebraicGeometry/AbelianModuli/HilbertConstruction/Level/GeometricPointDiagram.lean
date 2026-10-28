import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LevelPullbackGeometry

/-! # Geometric Point Diagram -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The geometric full-level equivalence intertwines the actual Yoneda
maps on every test scheme. This retains the ordered level, including
arbitrary disconnected tests, in the represented torsion isomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false

variable {S T : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) (f : T ⟶ S)
variable (l : (A.pullback f).FullLevel N)

theorem Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv_yoneda :
    yonedaGrp.map (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N f l).hom =
      (Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N f).hom ≫ l.hom ≫
        (A.torsionPullbackYonedaIso N f).inv :=
  congrArg Iso.hom
    (((yonedaGrpFullyFaithful (C := Over T)).isoEquiv
      (X := Grp.mk ((Over.pullback f).obj (Level.Scheme.constantFullLevelScheme g N S)))
      (Y := Grp.mk ((Over.pullback f).obj (A.torsionScheme N)))).apply_symm_apply
      (GroupIsomorphismData.isoTransportEquiv (Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N f)
        (A.torsionPullbackYonedaIso N f) l))

theorem Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv_diagram :
    yonedaGrp.map (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N f l).hom ≫
      (A.torsionPullbackYonedaIso N f).hom =
        (Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N f).hom ≫ l.hom := by
  rw [Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv_yoneda]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv_point (U : Over T)
    (q : U ⟶ (Over.pullback f).obj (Level.Scheme.constantFullLevelScheme g N S)) :
    (A.torsionPullbackYonedaIso N f).hom.app (.op U)
      (q ≫ (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv A N f l).hom.hom.hom) =
        l.hom.app (.op U) ((Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N f).hom.app (.op U) q) := by
  exact congrArg (fun (η : yonedaGrpObj ((Over.pullback f).obj
      (Level.Scheme.constantFullLevelScheme g N S)) ⟶ (A.pullback f).torsionFunctor N) =>
        (η.app (.op U)).hom q) (Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv_diagram A N f l)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
