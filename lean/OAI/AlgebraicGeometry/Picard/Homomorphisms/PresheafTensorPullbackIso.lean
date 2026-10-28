import OAI.AlgebraicGeometry.Picard.Homomorphisms.FreeTensorPullbackIso
import OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorPullbackNatural
import OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafGenerators

/-! # Presheaf Tensor Pullback Iso -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorPullbackIso

noncomputable section

/-! Arbitrary pullback preserves tensor products of module presheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local instance presheafTensorPullbackIsoLocal1 : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory
local instance presheafTensorPullbackIsoLocal2 : MonoidalCategory Y.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory

local instance presheafTensorPullbackIsoLocal3 : (PresheafTensorPullback.Construction.modulePresheafPullback f).IsLeftAdjoint :=
  (PresheafTensorPullback.Construction.modulePresheafAdjunction f).isLeftAdjoint

local instance presheafTensorPullbackIsoLocal4 (Z : Scheme.{u}) (M : Z.PresheafOfModules) :
    PreservesColimitsOfSize.{u, u} (tensorRight M) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u}
    (tensorRight (C := PresheafOfModules (Z.presheaf ⋙ forget₂ CommRingCat RingCat)) M))

local instance presheafTensorPullbackIsoLocal5 (Z : Scheme.{u}) (M : Z.PresheafOfModules) :
    PreservesColimitsOfSize.{u, u} (tensorLeft M) :=
  inferInstanceAs (PreservesColimitsOfSize.{u, u}
    (tensorLeft (C := PresheafOfModules (Z.presheaf ⋙ forget₂ CommRingCat RingCat)) M))

instance presheafTensorPullbackComparison_isIso (M N : Y.PresheafOfModules) :
    IsIso (PresheafTensorPullback.Construction.presheafTensorPullbackComparison f M N) := by
  apply PresheafGenerators.Construction.modulePresheafNatTrans_isIso_of_freeOpen (PresheafTensorPullbackNatural.Construction.presheafTensorPullbackRightComparison f N)
  intro U
  apply PresheafGenerators.Construction.modulePresheafNatTrans_isIso_of_freeOpen
    (PresheafTensorPullbackNatural.Construction.presheafTensorPullbackLeftComparison f (FreePresheafTensor.Construction.freeOpenModulePresheaf Y U))
  intro V
  exact FreeTensorPullbackIso.Construction.freeTensorPullbackComparison_isIso f U V

def presheafTensorPullbackIso (M N : Y.PresheafOfModules) :
    (PresheafTensorPullback.Construction.modulePresheafPullback f).obj (M ⊗ N) ≅
      (PresheafTensorPullback.Construction.modulePresheafPullback f).obj M ⊗ (PresheafTensorPullback.Construction.modulePresheafPullback f).obj N :=
  asIso (PresheafTensorPullback.Construction.presheafTensorPullbackComparison f M N)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorPullbackIso
