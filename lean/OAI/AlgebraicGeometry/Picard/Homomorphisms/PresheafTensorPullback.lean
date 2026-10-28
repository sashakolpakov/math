import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorSheafification
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-! # Presheaf Tensor Pullback -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorPullback

noncomputable section

/-! The tensor comparison for pullback of module presheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local instance presheafTensorPullbackLocal1 : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory
local instance presheafTensorPullbackLocal2 : MonoidalCategory Y.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory

abbrev modulePresheafPushforward : X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  PresheafOfModules.pushforward f.toRingCatSheafHom.hom

abbrev modulePresheafPullback : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.pullback f.toRingCatSheafHom.hom

abbrev modulePresheafAdjunction : modulePresheafPullback f ⊣ modulePresheafPushforward f :=
  PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom

def presheafPushforwardTensorMap (M N : X.PresheafOfModules) :
    (modulePresheafPushforward f).obj M ⊗ (modulePresheafPushforward f).obj N ⟶
      (modulePresheafPushforward f).obj (M ⊗ N) where
  app U := Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (f.app U.unop).hom)
    (M.obj (.op (f ⁻¹ᵁ U.unop))) (N.obj (.op (f ⁻¹ᵁ U.unop)))
  naturality {U V} h := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    change (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (f.app V.unop).hom) _ _)
        (((modulePresheafPushforward f).obj M ⊗ (modulePresheafPushforward f).obj N).map h (m ⊗ₜ n)) =
      ((modulePresheafPushforward f).obj (M ⊗ N)).map h
        ((Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (f.app U.unop).hom) _ _) (m ⊗ₜ n))
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul,
      ModuleCat.restrictScalars_μ_tmul, ModuleCat.restrictScalars_μ_tmul,
      PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    rfl

def presheafTensorPullbackComparison (M N : Y.PresheafOfModules) :
    (modulePresheafPullback f).obj (M ⊗ N) ⟶
      (modulePresheafPullback f).obj M ⊗ (modulePresheafPullback f).obj N :=
  ((modulePresheafAdjunction f).homEquiv _ _).symm
    (((modulePresheafAdjunction f).unit.app M ⊗ₘ (modulePresheafAdjunction f).unit.app N) ≫
      presheafPushforwardTensorMap f ((modulePresheafPullback f).obj M) ((modulePresheafPullback f).obj N))

theorem presheafTensorPullbackComparison_homEquiv (M N : Y.PresheafOfModules) :
    (modulePresheafAdjunction f).homEquiv _ _ (presheafTensorPullbackComparison f M N) =
      ((modulePresheafAdjunction f).unit.app M ⊗ₘ (modulePresheafAdjunction f).unit.app N) ≫
        presheafPushforwardTensorMap f ((modulePresheafPullback f).obj M) ((modulePresheafPullback f).obj N) :=
  Equiv.apply_symm_apply _ _

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorPullback
