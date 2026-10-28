import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupDescentIs
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.GeometricLevel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BaseChange

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.BaseChange.GroupBaseChange

noncomputable section

/-! Canonical base change of the actual constant and torsion group
schemes, with the group structures preserved by the pullback functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S S' : Scheme.{0}} {g N : ℕ}

def constantBaseChangeYonedaIso (f : S' ⟶ S) :
    yonedaGrpObj ((Over.pullback f).obj (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N S)) ≅
      yonedaGrpObj (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N S') :=
  GroupDescentIs.GroupBaseChange.baseChangeYonedaIso _ f ≪≫
    Functor.isoWhiskerLeft (Over.map f).op (HilbertConstruction.Geometric.GeometricLevel.constantFullLevelYonedaIso g N S) ≪≫
    (HilbertConstruction.Geometric.GeometricLevel.constantFullLevelYonedaIso g N S').symm

def constantBaseChangeIso (f : S' ⟶ S) :
    Grp.mk ((Over.pullback f).obj (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N S)) ≅
      Grp.mk (HilbertConstruction.Level.Scheme.constantFullLevelScheme g N S') :=
  (yonedaGrpFullyFaithful.isoEquiv).symm (constantBaseChangeYonedaIso f)

def torsionBaseChangeYonedaIso (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (N : ℕ) :
    yonedaGrpObj ((Over.pullback f).obj (A.torsionScheme N)) ≅
      yonedaGrpObj ((A.pullback f).torsionScheme N) :=
  GroupDescentIs.GroupBaseChange.baseChangeYonedaIso _ f ≪≫
    Functor.isoWhiskerLeft (Over.map f).op (A.torsionSchemeYonedaIso N) ≪≫
    (A.torsionBaseChangeIso f N).symm ≪≫
    ((A.pullback f).torsionSchemeYonedaIso N).symm

def torsionBaseChangeIso (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (N : ℕ) :
    Grp.mk ((Over.pullback f).obj (A.torsionScheme N)) ≅
      Grp.mk ((A.pullback f).torsionScheme N) :=
  (yonedaGrpFullyFaithful.isoEquiv).symm (torsionBaseChangeYonedaIso A f N)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Level.BaseChange.GroupBaseChange
