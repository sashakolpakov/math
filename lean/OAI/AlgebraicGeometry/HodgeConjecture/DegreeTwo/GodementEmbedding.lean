import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalStalkQuasiIso
import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Godement Embedding -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions

noncomputable section

/-! Every module sheaf embeds into the genuine flasque sheaf of all families of its stalk values. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.TopCat.Presheaf

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [Ring R] {X : TopCat.{0}}

def stalkFamilyPresheaf (F : TopCat.Sheaf (ModuleCat.{0} R) X) : X.Presheaf (ModuleCat.{0} R) where
  obj U := ModuleCat.of R (∀ x : U.unop, F.presheaf.stalk x.val)
  map {U W} i := ModuleCat.ofHom
    { toFun := fun s x => s (i.unop x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id U := by ext s x; rfl
  map_comp i j := by ext s x; rfl

theorem stalkFamilyPresheaf_isSheaf (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    (stalkFamilyPresheaf F).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget (ModuleCat.{0} R)) _).mpr
  exact TopCat.Presheaf.toTypes_isSheaf X (fun x => F.presheaf.stalk x)

def stalkFamilySheaf (F : TopCat.Sheaf (ModuleCat.{0} R) X) : TopCat.Sheaf (ModuleCat.{0} R) X :=
  ⟨stalkFamilyPresheaf F, stalkFamilyPresheaf_isSheaf F⟩

theorem stalkFamilySheaf_isFlasque (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    TopCat.Sheaf.IsFlasque (stalkFamilySheaf F) where
  epi {U W} i := by
    classical
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro s
    refine ⟨fun x => if hx : x.val ∈ W.unop then s ⟨x.val,hx⟩ else 0, ?_⟩
    funext x
    change (if hx : x.val ∈ W.unop then s ⟨x.val,hx⟩ else 0) = s x
    rw [dite_eq_left x.property]

def stalkFamilyEmbedding (F : TopCat.Sheaf (ModuleCat.{0} R) X) : F ⟶ stalkFamilySheaf F :=
  ⟨{ app U := ModuleCat.ofHom
       { toFun := fun s x => germ F.presheaf U.unop x.val x.property s
         map_add' := by intros; funext x; exact map_add _ _ _
         map_smul' := by intros; funext x; exact map_smul _ _ _ }
     naturality U W i := by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro s
       funext x
       exact ConcreteCategory.congr_hom (germ_res F.presheaf i.unop x.val x.property) s }⟩

theorem stalkFamilyEmbedding_mono (F : TopCat.Sheaf (ModuleCat.{0} R) X) :
    Mono (stalkFamilyEmbedding F) := by
  have : Mono (stalkFamilyEmbedding F).hom := by
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro U
    apply (ModuleCat.mono_iff_injective _).mpr
    intro s t h
    apply section_ext F U.unop
    intro x hx
    exact congrFun h ⟨x,hx⟩
  exact (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr this

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GodementEmbedding.Constructions
