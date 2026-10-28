import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.BaseChangeCoherence

/-! # Group Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupPullbackComposition

noncomputable section

/-! Composition of native pullbacks preserves the group structure for
any group object over a scheme, including disconnected universal groups. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj
universe u
variable {S T U : Scheme.{u}} (X : Over S) [GrpObj X] (f : T ⟶ S) (h : U ⟶ T)

def groupPullbackCompMonIso :
    Mon.mk ((Over.pullback (h ≫ f)).obj X) ≅
      Mon.mk ((Over.pullback h).obj ((Over.pullback f).obj X)) :=
  (Functor.mapMonNatIso (Over.pullbackComp h f)).app (Mon.mk X) ≪≫
    (Functor.mapMonCompIso (F := Over.pullback f) (G := Over.pullback h)).app (Mon.mk X)

def groupPullbackCompIso :
    (Over.pullback (h ≫ f)).obj X ≅ (Over.pullback h).obj ((Over.pullback f).obj X) :=
  (Mon.forget (Over U)).mapIso (groupPullbackCompMonIso X f h)

instance groupPullbackCompIso_isMonHom : IsMonHom (groupPullbackCompIso X f h).hom :=
  inferInstanceAs (IsMonHom (groupPullbackCompMonIso X f h).hom.hom)

instance groupPullbackCompIso_inv_isMonHom : IsMonHom (groupPullbackCompIso X f h).inv :=
  inferInstanceAs (IsMonHom (groupPullbackCompMonIso X f h).inv.hom)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GroupPullbackComposition
