import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupBaseChangePoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupIsomorphismData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.GeometricLevel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Level Pullback Geometry -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Full levels after arbitrary base change are exactly group-scheme isomorphisms between the pulled-back constant level scheme and the pulled-back torsion scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj

universe u

variable {S T : Scheme.{u}}

def Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso (g N : ℕ) (f : T ⟶ S) :
    yonedaGrpObj ((Over.pullback f).obj (Level.Scheme.constantFullLevelScheme g N S)) ≅
      Abelian.Schemes.AbelianScheme.constantLevelFunctor g N T :=
  GroupBaseChangePoints.groupBaseChangeYonedaIso (Level.Scheme.constantFullLevelScheme g N S) f ≪≫
    Functor.isoWhiskerLeft (Over.map f).op (Geometric.GeometricLevel.constantFullLevelYonedaIso g N S)

def Abelian.Schemes.AbelianScheme.torsionPullbackYonedaIso {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) (f : T ⟶ S) :
    yonedaGrpObj ((Over.pullback f).obj (A.torsionScheme N)) ≅ (A.pullback f).torsionFunctor N :=
  GroupBaseChangePoints.groupBaseChangeYonedaIso (A.torsionScheme N) f ≪≫
    Functor.isoWhiskerLeft (Over.map f).op (A.torsionSchemeYonedaIso N) ≪≫ (A.torsionBaseChangeIso f N).symm

def Abelian.Schemes.AbelianScheme.FullLevel.baseChangeGeometricEquiv {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S) (N : ℕ) (f : T ⟶ S) :
    (A.pullback f).FullLevel N ≃
      (Grp.mk ((Over.pullback f).obj (Level.Scheme.constantFullLevelScheme g N S)) ≅
        Grp.mk ((Over.pullback f).obj (A.torsionScheme N))) :=
  (GroupIsomorphismData.isoTransportEquiv (Level.LevelPullbackGeometry.constantFullLevelBaseChangeYonedaIso g N f) (A.torsionPullbackYonedaIso N f)).trans
    ((yonedaGrpFullyFaithful (C := Over T)).isoEquiv
      (X := Grp.mk ((Over.pullback f).obj (Level.Scheme.constantFullLevelScheme g N S)))
      (Y := Grp.mk ((Over.pullback f).obj (A.torsionScheme N)))).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
