import OAI.AlgebraicGeometry.Picard.Homomorphisms.FramedDescentScalars

/-! # Module Hom Transport -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomTransport

noncomputable section

/-! Transport morphisms between pullbacks along another scheme map.
The composition law is the native pseudofunctor coherence law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}

def moduleHomTransport
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    {T : Scheme.{u}} (t : T ⟶ X) (q : T ⟶ Y) (ht : t ≫ f = q) :
    (Scheme.Modules.pullback q).obj L ⟶ (Scheme.Modules.pullback q).obj M :=
  pullHom (F := PoincareBundle.Geometric.KernelLinearization.modulePullbacks) b t q q ht ht

theorem moduleHomTransport_native
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    {T : Scheme.{u}} (t : T ⟶ X) (q : T ⟶ Y) (ht : t ≫ f = q) :
    moduleHomTransport f b t q ht =
      (Scheme.Modules.pullbackComp t f ≪≫ Scheme.Modules.pullbackCongr ht).inv.app L ≫
        (Scheme.Modules.pullback t).map b ≫
          (Scheme.Modules.pullbackComp t f ≪≫ Scheme.Modules.pullbackCongr ht).hom.app M :=
  PoincareBundle.Geometric.PullHom.pullHom_eq b t q q ht ht

theorem moduleHomTransport_comp
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    {T T' : Scheme.{u}} (t : T ⟶ X) (q : T ⟶ Y) (ht : t ≫ f = q)
    (u : T' ⟶ T) (r : T' ⟶ Y) (hu : u ≫ q = r) :
    moduleHomTransport q (moduleHomTransport f b t q ht) u r hu =
      moduleHomTransport f b (u ≫ t) r (by rw [Category.assoc, ht, hu]) :=
  pullHom_pullHom (F := PoincareBundle.Geometric.KernelLinearization.modulePullbacks) (M₁ := L) (M₂ := M) (f₁ := f) (f₂ := f)
    b t q q u r r ht ht hu hu

theorem moduleHomTransport_congr
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    {T : Scheme.{u}} (t t' : T ⟶ X) (h : t = t') (q : T ⟶ Y)
    (ht : t ≫ f = q) (ht' : t' ≫ f = q) :
    moduleHomTransport f b t q ht = moduleHomTransport f b t' q ht' := by
  cases h
  rfl

theorem moduleHomTransport_injective {T : Scheme.{u}} (t : T ⟶ X) (q : T ⟶ Y)
    (ht : t ≫ f = q)
    (hfaith : Function.Injective ((Scheme.Modules.pullback t).map :
      ((Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M) → _)) :
    Function.Injective (fun b : (Scheme.Modules.pullback f).obj L ⟶
      (Scheme.Modules.pullback f).obj M => moduleHomTransport f b t q ht) := by
  intro a b hab
  change moduleHomTransport f a t q ht = moduleHomTransport f b t q ht at hab
  apply hfaith
  have h := congrArg (fun z =>
    (Scheme.Modules.pullbackComp t f ≪≫ Scheme.Modules.pullbackCongr ht).hom.app L ≫ z ≫
      (Scheme.Modules.pullbackComp t f ≪≫ Scheme.Modules.pullbackCongr ht).inv.app M) hab
  rw [moduleHomTransport_native f a t q ht, moduleHomTransport_native f b t q ht] at h
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app] at h
  change (Scheme.Modules.pullback t).map a ≫ 𝟙 _ = (Scheme.Modules.pullback t).map b ≫ 𝟙 _ at h
  rw [Category.comp_id, Category.comp_id] at h
  exact h

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomTransport
