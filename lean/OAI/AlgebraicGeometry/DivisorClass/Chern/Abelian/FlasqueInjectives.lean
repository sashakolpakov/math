import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.ResolutionClasses
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.SheafOfFunctions

/-! # Flasque Injectives -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.FlasqueInjectives

noncomputable section

/-! Injective abelian sheaves are flasque via the actual sheaf of stalk families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}}

def abelianStalkFamilyPresheaf (F : TopCat.Sheaf AddCommGrpCat.{0} X) : X.Presheaf AddCommGrpCat.{0} where
  obj U := AddCommGrpCat.of (∀ x : U.unop, ↥(stalk F.obj x.val))
  map i := AddCommGrpCat.ofHom {
    toFun s x := s (i.unop x)
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  map_id _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    rfl
  map_comp _ _ := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    rfl

theorem abelianStalkFamilyPresheaf_isSheaf (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    (abelianStalkFamilyPresheaf F).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).mpr
  exact TopCat.Presheaf.toTypes_isSheaf X (fun x => ↥(stalk F.obj x))

def abelianStalkFamilySheaf (F : TopCat.Sheaf AddCommGrpCat.{0} X) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  ⟨abelianStalkFamilyPresheaf F, abelianStalkFamilyPresheaf_isSheaf F⟩

theorem abelianStalkFamilySheaf_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    TopCat.Sheaf.IsFlasque (abelianStalkFamilySheaf F) where
  epi {U V} i := by
    classical
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    refine ⟨fun x => if hx : x.val ∈ V.unop then s ⟨x.val, hx⟩ else 0, ?_⟩
    funext x
    change (if hx : x.val ∈ V.unop then s ⟨x.val, hx⟩ else 0) = s x
    rw [dite_eq_left x.property]

def abelianStalkFamilyEmbedding (F : TopCat.Sheaf AddCommGrpCat.{0} X) : F ⟶ abelianStalkFamilySheaf F :=
  ObjectProperty.homMk {
    app U := AddCommGrpCat.ofHom {
      toFun s x := germ F.obj U.unop x.val x.property s
      map_zero' := by funext x; exact map_zero _
      map_add' := by intro s t; funext x; exact map_add _ _ _ }
    naturality := by
      intro U V i
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro s
      funext x
      exact ConcreteCategory.congr_hom (germ_res F.obj i.unop x.val x.property) s }

theorem abelianStalkFamilyEmbedding_mono (F : TopCat.Sheaf AddCommGrpCat.{0} X) :
    Mono (abelianStalkFamilyEmbedding F) := by
  apply (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  intro s t h
  apply section_ext F U.unop
  intro x hx
  exact congrFun h ⟨x, hx⟩

theorem abelianSheafFlasque_of_retract {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
    (i : F ⟶ G) (r : G ⟶ F) (hir : i ≫ r = 𝟙 F) [TopCat.Sheaf.IsFlasque G] :
    TopCat.Sheaf.IsFlasque F where
  epi {U V} j := by
    have hV : i.hom.app V ≫ r.hom.app V = 𝟙 _ := congrArg (fun f => f.hom.app V) hir
    have : Epi (r.hom.app V) := (show SplitEpi (r.hom.app V) from
      { section_ := i.hom.app V, id := hV }).epi
    have : Epi (r.hom.app U ≫ F.obj.map j) := by
      rw [← r.hom.naturality]
      infer_instance
    exact epi_of_epi (r.hom.app U) (F.obj.map j)

theorem injectiveAbelianSheaf_isFlasque (F : TopCat.Sheaf AddCommGrpCat.{0} X) [Injective F] :
    TopCat.Sheaf.IsFlasque F := by
  have := abelianStalkFamilyEmbedding_mono F
  have := abelianStalkFamilySheaf_isFlasque F
  exact abelianSheafFlasque_of_retract (abelianStalkFamilyEmbedding F)
    (Injective.factorThru (𝟙 F) (abelianStalkFamilyEmbedding F))
    (Injective.comp_factorThru (𝟙 F) (abelianStalkFamilyEmbedding F))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.FlasqueInjectives
