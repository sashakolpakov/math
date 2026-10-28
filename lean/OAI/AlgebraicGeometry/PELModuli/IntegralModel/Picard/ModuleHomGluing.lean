import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Module Hom Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomGluing.PicardModuleHomGluing

noncomputable section

/-! Global module morphisms are the global sections of the proved sheaf
of local module morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions.PicardFunctions
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf.PicardModuleHomSheaf

variable {X : Scheme.{u}} (M N : X.Modules)

def homFromOverTop (q : M.over ⊤ ⟶ N.over ⊤) : M ⟶ N where
  val :=
    { app U := q.val.app (op (Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top))))
      naturality {U V} f := by
        let j : Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top)) ⟶
            Over.mk (homOfLE (show U.unop ≤ ⊤ from le_top)) := Over.homMk f.unop
        exact q.val.naturality j.op }

def overTopHomEquiv : (M.over ⊤ ⟶ N.over ⊤) ≃ (M ⟶ N) where
  toFun := homFromOverTop M N
  invFun q := q.over ⊤
  left_inv q := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨V⟩
    obtain ⟨U, g, rfl⟩ := V.mk_surjective
    rfl
  right_inv q := by
    apply Scheme.Modules.hom_ext
    intro U
    rfl

def moduleHomGlobalEquiv : (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj.obj (op ⊤) ≃ (M ⟶ N) :=
  (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomOverEquiv M N ⊤).trans (overTopHomEquiv M N)

theorem moduleHomGlobalEquiv_symm_restrict (q : M ⟶ N) (U : X.Opens) :
    (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
        ((moduleHomGlobalEquiv M N).symm q) = ModuleHomSheaf.PicardModuleHomSheaf.moduleHomFromOver M N U (q.over U) := rfl

/-- Compatible local module maps glue uniquely to an actual global
module-sheaf morphism. Compatibility is tested in the existing Hom sheaf. -/
theorem existsUnique_hom_of_local_maps {ι : Type*} (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (q : ∀ i, (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj.obj (op (U i)))
    (hq : TopCat.Presheaf.IsCompatible (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj U q) :
    ∃! a : M ⟶ N, ∀ i, ModuleHomSheaf.PicardModuleHomSheaf.moduleHomFromOver M N (U i) (a.over (U i)) = q i := by
  let F : TopCat.Sheaf (Type u) X := ⟨(ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj, (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).property⟩
  obtain ⟨s, hs, hu⟩ := F.existsUnique_gluing' U ⊤
    (fun _ ↦ homOfLE le_top) hU q hq
  refine ⟨moduleHomGlobalEquiv M N s, ?_, ?_⟩
  · intro i
    rw [← moduleHomGlobalEquiv_symm_restrict, Equiv.symm_apply_apply]
    exact hs i
  · intro a ha
    apply (moduleHomGlobalEquiv M N).symm.injective
    rw [Equiv.symm_apply_apply]
    apply hu
    intro i
    rw [moduleHomGlobalEquiv_symm_restrict]
    exact ha i

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomGluing.PicardModuleHomGluing
