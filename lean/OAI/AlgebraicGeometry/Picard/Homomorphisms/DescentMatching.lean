import OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomTransport
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomBaseChange

/-! # Descent Matching -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.DescentMatching

noncomputable section

/-! A local descended map matches the original covering map after
transport to the common composite. This matching equation is preserved
by a further base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y U XU : Scheme.{u}} (f : X ⟶ Y) (g : XU ⟶ U)
variable (s : U ⟶ Y) (t : XU ⟶ X) (w : t ≫ f = g ≫ s)
variable {L M : Y.Modules}

theorem moduleHom_matching_of_square
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    (a : (Scheme.Modules.pullback s).obj L ⟶ (Scheme.Modules.pullback s).obj M)
    (ha : (Scheme.Modules.pullback g).map a =
      (ModuleHomBaseChange.Construction.nativeModuleDescentSquareIso f g s t w).inv.app L ≫
        (Scheme.Modules.pullback t).map b ≫ (ModuleHomBaseChange.Construction.nativeModuleDescentSquareIso f g s t w).hom.app M) :
    ModuleHomTransport.Construction.moduleHomTransport s a g (t ≫ f) w.symm = ModuleHomTransport.Construction.moduleHomTransport f b t (t ≫ f) rfl := by
  rw [ModuleHomTransport.Construction.moduleHomTransport_native s a g (t ≫ f) w.symm,
    ModuleHomTransport.Construction.moduleHomTransport_native f b t (t ≫ f) rfl, ha]
  simp only [ModuleHomBaseChange.Construction.nativeModuleDescentSquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]

theorem moduleHom_matching_baseChange
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    (a : (Scheme.Modules.pullback s).obj L ⟶ (Scheme.Modules.pullback s).obj M)
    (ha : ModuleHomTransport.Construction.moduleHomTransport s a g (t ≫ f) w.symm = ModuleHomTransport.Construction.moduleHomTransport f b t (t ≫ f) rfl)
    {V XV : Scheme.{u}} (j : V ⟶ U) (i : XV ⟶ XU) (g' : XV ⟶ V)
    (hij : i ≫ g = g' ≫ j) (s' : V ⟶ Y) (hs : j ≫ s = s')
    (t' : XV ⟶ X) (ht : i ≫ t = t') (w' : t' ≫ f = g' ≫ s') :
    ModuleHomTransport.Construction.moduleHomTransport s' (ModuleHomTransport.Construction.moduleHomTransport s a j s' hs) g' (t' ≫ f) w'.symm =
      ModuleHomTransport.Construction.moduleHomTransport f b t' (t' ≫ f) rfl := by
  have hi : i ≫ (t ≫ f) = t' ≫ f := (Category.assoc i t f).symm.trans (congrArg (· ≫ f) ht)
  have h₁ := ModuleHomTransport.Construction.moduleHomTransport_comp s a j s' hs g' (t' ≫ f) w'.symm
  have h₂ := ModuleHomTransport.Construction.moduleHomTransport_comp s a g (t ≫ f) w.symm i (t' ≫ f) hi
  have h₃ := ModuleHomTransport.Construction.moduleHomTransport_congr s a (g' ≫ j) (i ≫ g) hij.symm (t' ≫ f)
    (by rw [Category.assoc, hs, ← w']) (by rw [Category.assoc, ← w, hi])
  have h₄ := ModuleHomTransport.Construction.moduleHomTransport_comp f b t (t ≫ f) rfl i (t' ≫ f) hi
  have h₅ := ModuleHomTransport.Construction.moduleHomTransport_congr f b (i ≫ t) t' ht (t' ≫ f)
    (by rw [ht]) rfl
  exact h₁.trans (h₃.trans (h₂.symm.trans
    ((congrArg (fun c => ModuleHomTransport.Construction.moduleHomTransport (t ≫ f) c i (t' ≫ f) hi) ha).trans
      (h₄.trans h₅))))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.DescentMatching
