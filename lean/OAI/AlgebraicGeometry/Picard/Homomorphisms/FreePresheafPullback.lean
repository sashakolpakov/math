import OAI.AlgebraicGeometry.Picard.Homomorphisms.FreePresheafTensor

/-! # Free Presheaf Pullback -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FreePresheafPullback

noncomputable section

/-! Pullback of the free module on an open subspace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local instance freePresheafPullbackLocal1 : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory
local instance freePresheafPullbackLocal2 : MonoidalCategory Y.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory

local instance freePresheafPullbackLocal3 (Z : Scheme.{u}) (U : Z.Opensᵒᵖ) : CommRing (Z.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(Z, U.unop))

local instance freePresheafPullbackLocal4 (Z : Scheme.{u}) (M : Z.PresheafOfModules) (U : Z.Opensᵒᵖ) :
    Module Γ(Z, U.unop) (M.obj U) := (M.obj U).isModule

def pullbackFreeOpenCorepresentable (U : Y.Opens) :
    (PresheafTensorPullback.Construction.modulePresheafPushforward f ⋙ coyoneda.obj (op (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U))).CorepresentableBy
      ((PresheafTensorPullback.Construction.modulePresheafPullback f).obj (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U)) where
  homEquiv := (PresheafTensorPullback.Construction.modulePresheafAdjunction f).homEquiv _ _
  homEquiv_comp g h := (PresheafTensorPullback.Construction.modulePresheafAdjunction f).homEquiv_naturality_right h g

def freeOpenPullbackIso (U : Y.Opens) :
    (PresheafTensorPullback.Construction.modulePresheafPullback f).obj (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U) ≅
      FreePresheafTensor.Construction.freeOpenModulePresheaf X (f ⁻¹ᵁ U) :=
  (pullbackFreeOpenCorepresentable f U).uniqueUpToIso
    (PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy
      f.toRingCatSheafHom.hom U)

theorem freeOpenPullbackIso_homEquiv (U : Y.Opens) :
    (PresheafTensorPullback.Construction.modulePresheafAdjunction f).homEquiv _ _ (freeOpenPullbackIso f U).hom =
      PresheafOfModules.freeYonedaEquiv.symm (ModuleCat.freeMk (𝟙 (f ⁻¹ᵁ U))) := by
  simp [freeOpenPullbackIso, Functor.CorepresentableBy.uniqueUpToIso_hom,
    Coyoneda.fullyFaithful_preimage,
    pullbackFreeOpenCorepresentable,
    PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy]
  rfl

theorem freeOpenPullbackIso_unit_generator (U : Y.Opens) :
    (freeOpenPullbackIso f U).hom.app (op (f ⁻¹ᵁ U))
      (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U)).app (op U)
        (ModuleCat.freeMk (𝟙 U))) = ModuleCat.freeMk (𝟙 (f ⁻¹ᵁ U)) := by
  have h := congrArg (fun a => a.app (op U) (ModuleCat.freeMk (𝟙 U)))
    (freeOpenPullbackIso_homEquiv f U)
  erw [PresheafOfModules.freeYonedaEquiv_symm_app] at h
  exact h

theorem freeOpenHom_generator {Z : Scheme.{u}} {U W : Z.Opens}
    {M : Z.PresheafOfModules} (a : FreePresheafTensor.Construction.freeOpenModulePresheaf Z U ⟶ M) (h : W ⟶ U) :
    a.app (op W) (ModuleCat.freeMk h) =
      M.map h.op (a.app (op U) (ModuleCat.freeMk (𝟙 U))) := by
  have e := PresheafOfModules.naturality_apply a h.op (ModuleCat.freeMk (𝟙 U))
  erw [FreePresheafTensor.Construction.freeModulePresheaf_map_freeMk] at e
  simpa using e

theorem freeOpenTensorIso_hom_freeMk (Z : Scheme.{u}) (U V W : Z.Opens)
    (h : W ⟶ U) (k : W ⟶ V) :
    (FreePresheafTensor.Construction.freeOpenTensorIso Z U V).hom.app (op W) (ModuleCat.freeMk h ⊗ₜ ModuleCat.freeMk k) =
      ModuleCat.freeMk (homOfLE (le_inf (leOfHom h) (leOfHom k))) := by
  change (ModuleCat.free (Z.ringCatSheaf.obj.obj (op W))).map
      ((FreePresheafTensor.Construction.openYonedaProductIso Z U V).hom.app (op W))
      ((ModuleCat.FreeMonoidal.μIso (Z.ringCatSheaf.obj.obj (op W)) _ _).hom
        (ModuleCat.freeMk h ⊗ₜ ModuleCat.freeMk k)) = _
  erw [ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk, ModuleCat.free_map_apply]
  rfl

theorem freeOpenTensorIso_inv_freeMk (Z : Scheme.{u}) (U V W : Z.Opens) (h : W ⟶ U ⊓ V) :
    (FreePresheafTensor.Construction.freeOpenTensorIso Z U V).inv.app (op W) (ModuleCat.freeMk h) =
      ModuleCat.freeMk (h ≫ homOfLE inf_le_left) ⊗ₜ
        ModuleCat.freeMk (h ≫ homOfLE inf_le_right) := by
  change (ModuleCat.FreeMonoidal.μIso (Z.ringCatSheaf.obj.obj (op W)) _ _).inv
      ((ModuleCat.free (Z.ringCatSheaf.obj.obj (op W))).map
        ((FreePresheafTensor.Construction.openYonedaProductIso Z U V).inv.app (op W)) (ModuleCat.freeMk h)) = _
  erw [ModuleCat.free_map_apply, ModuleCat.FreeMonoidal.μIso_inv_freeMk]
  rfl

theorem presheafTensorPullbackComparison_unit_tmul (M N : Y.PresheafOfModules)
    (U : Y.Opens) (m : M.obj (op U)) (n : N.obj (op U)) :
    (PresheafTensorPullback.Construction.presheafTensorPullbackComparison f M N).app (op (f ⁻¹ᵁ U))
      (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app (M ⊗ N)).app (op U) (m ⊗ₜ n)) =
      (show ((PresheafTensorPullback.Construction.modulePresheafPullback f).obj M).obj (op (f ⁻¹ᵁ U)) from
        ((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app M).app (op U) m) ⊗ₜ[Γ(X, f ⁻¹ᵁ U)]
        (show ((PresheafTensorPullback.Construction.modulePresheafPullback f).obj N).obj (op (f ⁻¹ᵁ U)) from
          ((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app N).app (op U) n) := by
  have h := congrArg (fun a => a.app (op U) (m ⊗ₜ n))
    (PresheafTensorPullback.Construction.presheafTensorPullbackComparison_homEquiv f M N)
  change (PresheafTensorPullback.Construction.presheafTensorPullbackComparison f M N).app (op (f ⁻¹ᵁ U))
      (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app (M ⊗ N)).app (op U) (m ⊗ₜ n)) =
    (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (f.app U).hom) _ _)
      (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app M ⊗ₘ (PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app N).app
        (op U) (m ⊗ₜ n)) at h
  have ht := ModuleCat.MonoidalCategory.tensorHom_tmul
    (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app M).app (op U))
    (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app N).app (op U)) m n
  have ht' := congrArg (fun t =>
    (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (f.app U).hom)
      (((PresheafTensorPullback.Construction.modulePresheafPullback f).obj M).obj (op (f ⁻¹ᵁ U)))
      (((PresheafTensorPullback.Construction.modulePresheafPullback f).obj N).obj (op (f ⁻¹ᵁ U)))) t) ht
  exact h.trans (ht'.trans (ModuleCat.restrictScalars_μ_tmul (f.app U).hom
    (((PresheafTensorPullback.Construction.modulePresheafPullback f).obj M).obj (op (f ⁻¹ᵁ U)))
    (((PresheafTensorPullback.Construction.modulePresheafPullback f).obj N).obj (op (f ⁻¹ᵁ U)))
    (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app M).app (op U) m)
    (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app N).app (op U) n)))

theorem freeOpenPullbackIso_unit_freeMk {U W : Y.Opens} (h : W ⟶ U) :
    (freeOpenPullbackIso f U).hom.app (op (f ⁻¹ᵁ W))
      (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U)).app (op W)
        (ModuleCat.freeMk h)) = ModuleCat.freeMk ((TopologicalSpace.Opens.map f.base).map h) := by
  have e := freeOpenHom_generator
    ((PresheafTensorPullback.Construction.modulePresheafAdjunction f).homEquiv _ _ (freeOpenPullbackIso f U).hom) h
  change (freeOpenPullbackIso f U).hom.app (op (f ⁻¹ᵁ W))
      (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U)).app (op W)
        (ModuleCat.freeMk h)) =
    (FreePresheafTensor.Construction.freeOpenModulePresheaf X (f ⁻¹ᵁ U)).map ((TopologicalSpace.Opens.map f.base).map h).op
      ((freeOpenPullbackIso f U).hom.app (op (f ⁻¹ᵁ U))
        (((PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.app (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U)).app (op U)
          (ModuleCat.freeMk (𝟙 U)))) at e
  rw [freeOpenPullbackIso_unit_generator] at e
  erw [FreePresheafTensor.Construction.freeModulePresheaf_map_freeMk] at e
  simpa using e

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FreePresheafPullback
