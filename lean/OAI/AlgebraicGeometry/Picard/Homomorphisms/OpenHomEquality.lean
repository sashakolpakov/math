import OAI.AlgebraicGeometry.Picard.Homomorphisms.PullbackHomGluing
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomTransport

/-! # Open Hom Equality -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenHomEquality

noncomputable section

/-! Equality of module morphisms is local on the source scheme.
Transport detects the corresponding equality after pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u v

theorem moduleHom_eq_of_open_cover {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type v} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i) (a b : M ⟶ N)
    (hab : ∀ i, (Scheme.Modules.pullback (U i).ι).map a = (Scheme.Modules.pullback (U i).ι).map b) :
    a = b := by
  apply (GlobalHomSections.Construction.moduleHomGlobalSectionEquiv M N).injective
  apply (InternalHom.Construction.moduleInternalHom M N).isSheaf.section_ext
  intro x _
  obtain ⟨i, hi⟩ := hU x
  refine ⟨U i, le_top, hi, ?_⟩
  exact (PullbackHomGluing.Construction.pullbackHomOnOpenEquiv_map M N (U i) a).symm.trans
    ((congrArg (PullbackHomGluing.Construction.pullbackHomOnOpenEquiv M N (U i)) (hab i)).trans
      (PullbackHomGluing.Construction.pullbackHomOnOpenEquiv_map M N (U i) b))

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}

theorem moduleHomTransport_map_eq_of_eq
    (a b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    {T : Scheme.{u}} (t : T ⟶ X) (q : T ⟶ Y) (ht : t ≫ f = q)
    (hab : ModuleHomTransport.Construction.moduleHomTransport f a t q ht = ModuleHomTransport.Construction.moduleHomTransport f b t q ht) :
    (Scheme.Modules.pullback t).map a = (Scheme.Modules.pullback t).map b := by
  have h := congrArg (fun z =>
    (Scheme.Modules.pullbackComp t f ≪≫ Scheme.Modules.pullbackCongr ht).hom.app L ≫ z ≫
      (Scheme.Modules.pullbackComp t f ≪≫ Scheme.Modules.pullbackCongr ht).inv.app M) hab
  rw [ModuleHomTransport.Construction.moduleHomTransport_native f a t q ht, ModuleHomTransport.Construction.moduleHomTransport_native f b t q ht] at h
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app] at h
  change (Scheme.Modules.pullback t).map a ≫ 𝟙 _ = (Scheme.Modules.pullback t).map b ≫ 𝟙 _ at h
  rw [Category.comp_id, Category.comp_id] at h
  exact h

theorem moduleHomTransport_map (a : L ⟶ M)
    {T : Scheme.{u}} (t : T ⟶ X) (q : T ⟶ Y) (ht : t ≫ f = q) :
    ModuleHomTransport.Construction.moduleHomTransport f ((Scheme.Modules.pullback f).map a) t q ht =
      (Scheme.Modules.pullback q).map a := by
  rw [ModuleHomTransport.Construction.moduleHomTransport_native]
  exact NatIso.naturality_1 (Scheme.Modules.pullbackComp t f ≪≫ Scheme.Modules.pullbackCongr ht) a

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenHomEquality
