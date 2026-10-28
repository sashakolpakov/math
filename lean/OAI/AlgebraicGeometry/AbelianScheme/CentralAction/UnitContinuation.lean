import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullbackUnits

/-! # Unit Continuation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.UnitContinuation

noncomputable section

/-! The adjoint of a local comparison is compatible with native
pullHom. This retains the section maps needed for ordinary sheaf gluing. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Construction

universe u
variable {S : Scheme.{u}} {X T W : Over S}

theorem linePushforwardCongr_refl {A B : Scheme.{u}} (f : A ⟶ B) :
    Scheme.Modules.pushforwardCongr (rfl : f = f) = Iso.refl _ := by
  apply Iso.ext
  ext M U x
  simp

def linePushforwardSquareIso (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f') :
    Scheme.Modules.pushforward g.left ⋙ Scheme.Modules.pushforward f.left ≅
      Scheme.Modules.pushforward f'.left :=
  Scheme.Modules.pushforwardComp g.left f.left ≪≫
    Scheme.Modules.pushforwardCongr (congrArg Over.Hom.left hf)

theorem line_square_unit (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f')
    (M : X.left.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f.left).comp
        (Scheme.Modules.pullbackPushforwardAdjunction g.left)).unit.app M ≫
      (linePushforwardSquareIso f g f' hf).hom.app
        ((Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback f.left).obj M)) =
    (Scheme.Modules.pullbackPushforwardAdjunction f'.left).unit.app M ≫
      (Scheme.Modules.pushforward f'.left).map ((LinePullbackFormula.Construction.linePullbackSquareIso f g f' hf).inv.app M) := by
  subst f'
  simp only [linePushforwardSquareIso, linePushforwardCongr_refl, Iso.trans_refl,
    LinePullbackFormula.Construction.linePullbackSquareIso, Scheme.Modules.pullbackCongr, eqToIso_refl]
  exact PullbackUnits.Construction.module_pullback_comp_unit g.left f.left M

def lineUnitContinuation (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f')
    (M : X.left.Modules) :
    (Scheme.Modules.pushforward f.left).obj ((Scheme.Modules.pullback f.left).obj M) ⟶
      (Scheme.Modules.pushforward f'.left).obj ((Scheme.Modules.pullback f'.left).obj M) :=
  (Scheme.Modules.pushforward f.left).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
        ((Scheme.Modules.pullback f.left).obj M)) ≫
    (linePushforwardSquareIso f g f' hf).hom.app
      ((Scheme.Modules.pullback g.left).obj ((Scheme.Modules.pullback f.left).obj M)) ≫
    (Scheme.Modules.pushforward f'.left).map ((LinePullbackFormula.Construction.linePullbackSquareIso f g f' hf).hom.app M)

theorem lineUnitContinuation_unit
    (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f') (M : X.left.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.app M ≫
        lineUnitContinuation f g f' hf M =
      (Scheme.Modules.pullbackPushforwardAdjunction f'.left).unit.app M := by
  have h := line_square_unit f g f' hf M
  simp only [Adjunction.comp_unit_app] at h
  dsimp only [lineUnitContinuation]
  rw [← Category.assoc, ← Category.assoc, h, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

theorem lineUnitContinuation_pullHom
    (f : T ⟶ X) (g : W ⟶ T) (f' : W ⟶ X) (hf : g ≫ f = f')
    (L M : X.left.Modules)
    (a : (Scheme.Modules.pullback f.left).obj L ⟶ (Scheme.Modules.pullback f.left).obj M) :
    (Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.app L ≫
        (Scheme.Modules.pushforward f.left).map a ≫ lineUnitContinuation f g f' hf M =
      (Scheme.Modules.pullbackPushforwardAdjunction f'.left).unit.app L ≫
        (Scheme.Modules.pushforward f'.left).map
          (pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) a g f' f' hf hf) := by
  rw [LinePullbackFormula.Construction.linePullHom_formula]
  let R := Scheme.Modules.pushforward f.left
  let R' := Scheme.Modules.pushforward f'.left
  let G := Scheme.Modules.pullback g.left
  let J := Scheme.Modules.pushforward g.left
  let c := LinePullbackFormula.Construction.linePullbackSquareIso f g f' hf
  let d := linePushforwardSquareIso f g f' hf
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.naturality a
  simp only [Functor.id_map, Functor.comp_map] at hn
  have hd := d.hom.naturality (G.map a)
  have hu := line_square_unit f g f' hf L
  simp only [Adjunction.comp_unit_app] at hu
  dsimp only [lineUnitContinuation]
  change _ ≫ R.map a ≫ R.map _ ≫ d.hom.app _ ≫ R'.map (c.hom.app M) =
    _ ≫ R'.map (c.inv.app L ≫ G.map a ≫ c.hom.app M)
  rw [← R.map_comp_assoc, hn, R.map_comp_assoc]
  change _ ≫ R.map _ ≫ (J ⋙ R).map (G.map a) ≫ d.hom.app _ ≫ _ = _
  erw [reassoc_of% hd]
  erw [← Category.assoc, ← Category.assoc, hu]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.UnitContinuation
