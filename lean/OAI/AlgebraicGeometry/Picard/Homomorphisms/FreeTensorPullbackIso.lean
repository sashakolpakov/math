import OAI.AlgebraicGeometry.Picard.Homomorphisms.FreePresheafPullback

/-! # Free Tensor Pullback Iso -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FreeTensorPullbackIso

noncomputable section

/-! The tensor-pullback comparison is invertible on free open generators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local instance freeTensorPullbackIsoLocal1 : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory
local instance freeTensorPullbackIsoLocal2 : MonoidalCategory Y.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory

theorem freeTensorPullbackComparison (U V : Y.Opens) :
    PresheafTensorPullback.Construction.presheafTensorPullbackComparison f (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U) (FreePresheafTensor.Construction.freeOpenModulePresheaf Y V) ≫
        ((FreePresheafPullback.Construction.freeOpenPullbackIso f U).hom ⊗ₘ (FreePresheafPullback.Construction.freeOpenPullbackIso f V).hom) ≫
          (FreePresheafTensor.Construction.freeOpenTensorIso X (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)).hom =
      (PresheafTensorPullback.Construction.modulePresheafPullback f).map (FreePresheafTensor.Construction.freeOpenTensorIso Y U V).hom ≫
        (FreePresheafPullback.Construction.freeOpenPullbackIso f (U ⊓ V)).hom := by
  apply ((PresheafTensorPullback.Construction.modulePresheafAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  erw [(PresheafTensorPullback.Construction.modulePresheafAdjunction f).homEquiv_naturality_left
    (FreePresheafTensor.Construction.freeOpenTensorIso Y U V).hom (FreePresheafPullback.Construction.freeOpenPullbackIso f (U ⊓ V)).hom]
  apply (cancel_epi (FreePresheafTensor.Construction.freeOpenTensorIso Y U V).inv).mp
  erw [(FreePresheafTensor.Construction.freeOpenTensorIso Y U V).inv_hom_id_assoc]
  apply PresheafOfModules.freeYonedaEquiv.injective
  rw [FreePresheafPullback.Construction.freeOpenPullbackIso_homEquiv f (U ⊓ V)]
  conv_rhs => erw [Equiv.apply_symm_apply]
  change (FreePresheafTensor.Construction.freeOpenTensorIso X (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)).hom.app (op (f ⁻¹ᵁ (U ⊓ V)))
      (((FreePresheafPullback.Construction.freeOpenPullbackIso f U).hom ⊗ₘ (FreePresheafPullback.Construction.freeOpenPullbackIso f V).hom).app (op (f ⁻¹ᵁ (U ⊓ V)))
        ((PresheafTensorPullback.Construction.presheafTensorPullbackComparison f (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U) (FreePresheafTensor.Construction.freeOpenModulePresheaf Y V)).app
          (op (f ⁻¹ᵁ (U ⊓ V)))
          (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app
            (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U ⊗ FreePresheafTensor.Construction.freeOpenModulePresheaf Y V)).app (op (U ⊓ V))
            ((FreePresheafTensor.Construction.freeOpenTensorIso Y U V).inv.app (op (U ⊓ V)) (ModuleCat.freeMk (𝟙 (U ⊓ V))))))) =
    ModuleCat.freeMk (𝟙 (f ⁻¹ᵁ (U ⊓ V)))
  rw [FreePresheafPullback.Construction.freeOpenTensorIso_inv_freeMk]
  erw [FreePresheafPullback.Construction.presheafTensorPullbackComparison_unit_tmul]
  erw [PresheafOfModulesOfCommRing.Monoidal.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul]
  erw [FreePresheafPullback.Construction.freeOpenPullbackIso_unit_freeMk, FreePresheafPullback.Construction.freeOpenPullbackIso_unit_freeMk]
  erw [FreePresheafPullback.Construction.freeOpenTensorIso_hom_freeMk]
  congr 1

theorem freeTensorPullbackComparison_isIso (U V : Y.Opens) :
    IsIso (PresheafTensorPullback.Construction.presheafTensorPullbackComparison f
      (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U) (FreePresheafTensor.Construction.freeOpenModulePresheaf Y V)) := by
  have : IsIso (PresheafTensorPullback.Construction.presheafTensorPullbackComparison f
      (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U) (FreePresheafTensor.Construction.freeOpenModulePresheaf Y V) ≫
      ((FreePresheafPullback.Construction.freeOpenPullbackIso f U).hom ⊗ₘ (FreePresheafPullback.Construction.freeOpenPullbackIso f V).hom) ≫
        (FreePresheafTensor.Construction.freeOpenTensorIso X (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)).hom) := by
    rw [freeTensorPullbackComparison]
    exact (inferInstance : IsIso
      (((PresheafTensorPullback.Construction.modulePresheafPullback f).mapIso (FreePresheafTensor.Construction.freeOpenTensorIso Y U V) ≪≫
        FreePresheafPullback.Construction.freeOpenPullbackIso f (U ⊓ V)).hom))
  exact IsIso.of_isIso_comp_right _
    (((FreePresheafPullback.Construction.freeOpenPullbackIso f U).hom ⊗ₘ (FreePresheafPullback.Construction.freeOpenPullbackIso f V).hom) ≫
      (FreePresheafTensor.Construction.freeOpenTensorIso X (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)).hom)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FreeTensorPullbackIso
