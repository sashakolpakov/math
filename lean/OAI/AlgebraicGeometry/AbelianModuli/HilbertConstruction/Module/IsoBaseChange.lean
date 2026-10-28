import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoPresheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.HomBaseChange

/-! # Iso Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoBaseChange

noncomputable section

/-! The presheaf of actual module isomorphisms is compatible with changing the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def moduleIsoBaseChangeEquiv (g : Y ⟶ X) (M N : X.Modules) (T : Over Y) :
    (IsoPresheaf.moduleIsoPresheaf ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N)).obj (.op T) ≃
      (IsoPresheaf.moduleIsoPresheaf M N).obj (.op ((Over.map g).obj T)) :=
  Iso.isoCongr ((Scheme.Modules.pullbackComp T.hom g).app M)
    ((Scheme.Modules.pullbackComp T.hom g).app N)

theorem moduleIsoBaseChangeEquiv_naturality (g : Y ⟶ X) (M N : X.Modules) {U V : Over Y}
    (a : U ⟶ V)
    (e : (IsoPresheaf.moduleIsoPresheaf ((Scheme.Modules.pullback g).obj M)
      ((Scheme.Modules.pullback g).obj N)).obj (.op V)) :
    moduleIsoBaseChangeEquiv g M N U (IsoSlicePullback.moduleIsoPullbackAlong a e) =
      IsoSlicePullback.moduleIsoPullbackAlong ((Over.map g).map a) (moduleIsoBaseChangeEquiv g M N V e) := by
  change (Scheme.Modules.pullback V.hom).obj ((Scheme.Modules.pullback g).obj M) ≅
    (Scheme.Modules.pullback V.hom).obj ((Scheme.Modules.pullback g).obj N) at e
  apply Iso.ext
  exact HomBaseChange.moduleHomBaseChangeEquiv_naturality g M N a e.hom

def moduleIsoBaseChangeIso (g : Y ⟶ X) (M N : X.Modules) :
    IsoPresheaf.moduleIsoPresheaf ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj N) ≅
      (Over.map g).op ⋙ IsoPresheaf.moduleIsoPresheaf M N :=
  NatIso.ofComponents (fun T => (moduleIsoBaseChangeEquiv g M N T.unop).toIso) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro e
    exact moduleIsoBaseChangeEquiv_naturality g M N f.unop e)

theorem moduleIsoPullbackAlong_of_map {U V : Over X} (a : U ⟶ V) {M N : X.Modules} (e : M ≅ N) :
    IsoSlicePullback.moduleIsoPullbackAlong a ((Scheme.Modules.pullback V.hom).mapIso e) =
      (Scheme.Modules.pullback U.hom).mapIso e := by
  apply Iso.ext
  exact HomPresheaf.moduleMapPullbackAlong_of_map a e.hom

def globalModuleIsoSection {X : Scheme.{u}} (M N : X.Modules) (e : M ≅ N) :
    (IsoPresheaf.moduleIsoPresheaf M N).sections where
  val T := (Scheme.Modules.pullback T.unop.hom).mapIso e
  property f := moduleIsoPullbackAlong_of_map f.unop e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoBaseChange
