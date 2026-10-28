import OAI.RepresentationTheory.Theta.Geometric.Pullback.FrameComposition

/-! # Associativity -/

namespace OAI.RepresentationTheory.Theta.Geometric.Pullback.Associativity

noncomputable section

/-! The canonical threefold pullback comparison, specialized from the
module-sheaf adjunction coherence theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullbackComp_assoc {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Functor.isoWhiskerLeft (Scheme.Modules.pullback h) (Scheme.Modules.pullbackComp f g) ≪≫
      Scheme.Modules.pullbackComp (f ≫ g) h =
    (Functor.associator (Scheme.Modules.pullback h) (Scheme.Modules.pullback g) (Scheme.Modules.pullback f)).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.pullbackComp g h) (Scheme.Modules.pullback f) ≪≫
        Scheme.Modules.pullbackComp f (g ≫ h) := by
  let : (SheafOfModules.pushforward h.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward h).IsRightAdjoint
  let : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward g).IsRightAdjoint
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  exact SheafOfModules.pullback_assoc h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom

theorem pullbackComp_assoc_app {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Z.Modules) :
    ((Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M)).hom ≫
      ((Scheme.Modules.pullbackComp (f ≫ g) h).app M).hom =
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).app M).hom ≫
      ((Scheme.Modules.pullbackComp f (g ≫ h)).app M).hom := by
  have he := congrArg (fun e => (e.app M).hom) (pullbackComp_assoc f g h)
  change ((Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M)).hom ≫
      ((Scheme.Modules.pullbackComp (f ≫ g) h).app M).hom =
    (𝟙 _) ≫ (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).app M).hom ≫
      ((Scheme.Modules.pullbackComp f (g ≫ h)).app M).hom at he
  simpa only [Category.id_comp] using he

end

end OAI.RepresentationTheory.Theta.Geometric.Pullback.Associativity
