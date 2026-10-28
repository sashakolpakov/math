import OAI.RepresentationTheory.Theta.Geometric.Pullback.Associativity

/-! # Factored Pullback Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.FactoredPullbackFrames

noncomputable section

/-! Successive factorizations give the same native pullback frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def factoredPullbackFrame {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (e : (Scheme.Modules.pullback g).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X :=
  ((Scheme.Modules.pullbackComp f g).app M).symm ≪≫ Pullback.FrameComposition.pullbackGlobalFrame f e

theorem pullbackComp_assoc_inv_app {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Z.Modules) :
    ((Scheme.Modules.pullbackComp f (g ≫ h)).app M).inv ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).app M).inv =
    ((Scheme.Modules.pullbackComp (f ≫ g) h).app M).inv ≫
      ((Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M)).inv := by
  let e := (Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M) ≪≫
    (Scheme.Modules.pullbackComp (f ≫ g) h).app M
  let d := (Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullbackComp g h).app M) ≪≫
    (Scheme.Modules.pullbackComp f (g ≫ h)).app M
  have hd : e = d := Iso.ext (Pullback.Associativity.pullbackComp_assoc_app f g h M)
  exact congrArg Iso.inv hd.symm

set_option backward.isDefEq.respectTransparency false in
theorem factoredPullbackFrame_comp {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    {M : Z.Modules} (e : (Scheme.Modules.pullback h).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y) :
    factoredPullbackFrame f (g ≫ h) (factoredPullbackFrame g h e) =
      factoredPullbackFrame (f ≫ g) h e := by
  apply Iso.ext
  have he := congrArg Iso.hom (Pullback.FrameComposition.pullbackGlobalFrame_comp f g e)
  change ((Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M)).hom ≫
    (Pullback.FrameComposition.pullbackGlobalFrame (f ≫ g) e).hom = (Pullback.FrameComposition.pullbackGlobalFrame f (Pullback.FrameComposition.pullbackGlobalFrame g e)).hom at he
  let a := (Scheme.Modules.pullbackComp (f ≫ g) h).app M
  let b := (Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M)
  have hcancel : (a.inv ≫ b.inv) ≫ (Pullback.FrameComposition.pullbackGlobalFrame f (Pullback.FrameComposition.pullbackGlobalFrame g e)).hom =
      a.inv ≫ (Pullback.FrameComposition.pullbackGlobalFrame (f ≫ g) e).hom := by
    have hh := congrArg (fun t => (a.inv ≫ b.inv) ≫ t) he.symm
    exact hh.trans (by simp only [b, Category.assoc, Iso.inv_hom_id_assoc])
  calc
    _ = (((Scheme.Modules.pullbackComp f (g ≫ h)).app M).inv ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).app M).inv) ≫
        (Pullback.FrameComposition.pullbackGlobalFrame f (Pullback.FrameComposition.pullbackGlobalFrame g e)).hom := by
      simp only [factoredPullbackFrame, Iso.trans_hom, Iso.symm_hom, Pullback.FrameComposition.pullbackGlobalFrame,
        Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    _ = (a.inv ≫ b.inv) ≫ (Pullback.FrameComposition.pullbackGlobalFrame f (Pullback.FrameComposition.pullbackGlobalFrame g e)).hom :=
      congrArg (fun t => t ≫ (Pullback.FrameComposition.pullbackGlobalFrame f (Pullback.FrameComposition.pullbackGlobalFrame g e)).hom)
        (pullbackComp_assoc_inv_app f g h M)
    _ = _ := hcancel

set_option backward.isDefEq.respectTransparency false in
theorem factoredPullbackFrame_assoc {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    {M : Z.Modules} (e : (Scheme.Modules.pullback (g ≫ h)).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj X) :
    (Scheme.Modules.pullbackComp (f ≫ g) h).app M ≪≫ factoredPullbackFrame f (g ≫ h) e =
      factoredPullbackFrame f g ((Scheme.Modules.pullbackComp g h).app M ≪≫ e) := by
  let a := (Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M)
  let b := (Scheme.Modules.pullbackComp (f ≫ g) h).app M
  let c := (Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullbackComp g h).app M)
  let d := (Scheme.Modules.pullbackComp f (g ≫ h)).app M
  have he : a.hom ≫ b.hom = c.hom ≫ d.hom := Pullback.Associativity.pullbackComp_assoc_app f g h M
  have hc : b.hom ≫ d.inv = a.inv ≫ c.hom := by
    have he' := congrArg (fun t => a.inv ≫ t ≫ d.inv) he
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using he'
  apply Iso.ext
  calc
    _ = (b.hom ≫ d.inv) ≫ (Pullback.FrameComposition.pullbackGlobalFrame f e).hom := by
      simp only [b, d, factoredPullbackFrame, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    _ = (a.inv ≫ c.hom) ≫ (Pullback.FrameComposition.pullbackGlobalFrame f e).hom :=
      congrArg (fun t => t ≫ (Pullback.FrameComposition.pullbackGlobalFrame f e).hom) hc
    _ = _ := by
      simp only [a, c, factoredPullbackFrame, Pullback.FrameComposition.pullbackGlobalFrame, Iso.trans_hom, Iso.symm_hom,
        Functor.mapIso_hom, Functor.map_comp, Category.assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.FactoredPullbackFrames
