import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomGluing

/-! # Open Hom Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenHomComparison.PicardOpenHomComparison

noncomputable section

/-! Open-slice module maps and actual scheme pullback maps agree.
This transports the proved Zariski gluing to native pullback morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.GlobalFunctions.PicardFunctions
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomSheaf.PicardModuleHomSheaf

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ModuleHomGluing.PicardModuleHomGluing

variable {X : Scheme.{u}} (M N : X.Modules)

def openModuleIso (U : X.Opens) :
    SheafOfModules.overFunctor X.ringCatSheaf U ⋙ (Scheme.Modules.overEquiv U).functor ≅
      Scheme.Modules.pullback U.ι :=
  Scheme.Modules.overFunctorEquiv U ≪≫ Scheme.Modules.restrictFunctorIsoPullback U.ι

def openHomEquiv (U : X.Opens) :
    (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj.obj (op U) ≃
      ((Scheme.Modules.pullback U.ι).obj M ⟶ (Scheme.Modules.pullback U.ι).obj N) :=
  (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomOverEquiv M N U).trans
    ((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv.trans
      (((openModuleIso U).app M).homCongr ((openModuleIso U).app N)))

theorem openHomEquiv_global (q : M ⟶ N) (U : X.Opens) :
    openHomEquiv M N U (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomFromOver M N U (q.over U)) =
      (Scheme.Modules.pullback U.ι).map q := by
  let β := openModuleIso U
  have hq := β.hom.naturality q
  change (β.app M).inv ≫
    ((SheafOfModules.overFunctor X.ringCatSheaf U ⋙ (Scheme.Modules.overEquiv U).functor).map q) ≫
      (β.app N).hom = _
  exact (congrArg (fun a ↦ (β.app M).inv ≫ a) hq).trans ((β.app M).inv_hom_id_assoc _)

theorem hom_eq_of_open_pullbacks {ι : Type*} (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U) (a b : M ⟶ N)
    (hab : ∀ i, (Scheme.Modules.pullback (U i).ι).map a = (Scheme.Modules.pullback (U i).ι).map b) :
    a = b := by
  apply (ModuleHomGluing.PicardModuleHomGluing.moduleHomGlobalEquiv M N).symm.injective
  let F : TopCat.Sheaf (Type u) X := ⟨(ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj, (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).property⟩
  apply F.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) hU
  intro i
  change (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op
      ((ModuleHomGluing.PicardModuleHomGluing.moduleHomGlobalEquiv M N).symm a) =
    (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op
      ((ModuleHomGluing.PicardModuleHomGluing.moduleHomGlobalEquiv M N).symm b)
  rw [ModuleHomGluing.PicardModuleHomGluing.moduleHomGlobalEquiv_symm_restrict, ModuleHomGluing.PicardModuleHomGluing.moduleHomGlobalEquiv_symm_restrict]
  apply (openHomEquiv M N (U i)).injective
  rw [openHomEquiv_global, openHomEquiv_global, hab i]

/-- Actual native pullback morphisms glue once their corresponding local
module maps agree on intersections. -/
theorem existsUnique_hom_of_open_pullbacks {ι : Type*} (U : ι → X.Opens)
    (hU : (⊤ : X.Opens) ≤ iSup U)
    (q : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ⟶
      (Scheme.Modules.pullback (U i).ι).obj N)
    (hq : TopCat.Presheaf.IsCompatible (ModuleHomSheaf.PicardModuleHomSheaf.moduleHomTypeSheaf M N).obj U
      (fun i ↦ (openHomEquiv M N (U i)).symm (q i))) :
    ∃! a : M ⟶ N, ∀ i, (Scheme.Modules.pullback (U i).ι).map a = q i := by
  obtain ⟨a, ha, hu⟩ := ModuleHomGluing.PicardModuleHomGluing.existsUnique_hom_of_local_maps M N U hU
    (fun i ↦ (openHomEquiv M N (U i)).symm (q i)) hq
  refine ⟨a, ?_, ?_⟩
  · intro i
    exact (openHomEquiv_global M N a (U i)).symm.trans
      ((congrArg (openHomEquiv M N (U i)) (ha i)).trans
        ((openHomEquiv M N (U i)).apply_symm_apply (q i)))
  · intro b hb
    apply hu
    intro i
    apply (openHomEquiv M N (U i)).injective
    rw [openHomEquiv_global, Equiv.apply_symm_apply, hb i]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.OpenHomComparison.PicardOpenHomComparison
