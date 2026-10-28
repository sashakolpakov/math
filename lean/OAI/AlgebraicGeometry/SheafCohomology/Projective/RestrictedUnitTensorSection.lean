import OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalTensorSectionCoherence

/-! # Restricted Unit Tensor Section -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictedUnitTensorSection

noncomputable section

/-! The local unit section and the unitor on restricted global sections. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
local instance restrictedUnitTensorMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem localMonoidalUnitSection_eq_restrict (X : Scheme.{u}) (U : X.Opens) :
    PowerCancellationPairing.localMonoidalUnitSection X U =
      (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (TensorSections.monoidalUnitSection X) := by
  have h := PresheafOfModules.naturality_apply (TensorSections.monoidalUnitObjIso X).inv.val
    (homOfLE (le_top : U ≤ ⊤)).op (show Γ(X, ⊤) from 1)
  change (TensorSections.monoidalUnitObjIso X).inv.val.app (op U)
    (X.presheaf.map (homOfLE le_top).op 1) = _ at h
  rw [map_one] at h
  exact h

theorem leftUnitor_tensorSection_restrict {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (x : Γ(M, ⊤)) :
    (λ_ M).hom.val.app (op U)
      (TensorSections.tensorSection (𝟙_ X.Modules) M U (PowerCancellationPairing.localMonoidalUnitSection X U)
        (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x)) =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x := by
  rw [localMonoidalUnitSection_eq_restrict]
  have h := PresheafOfModules.naturality_apply (λ_ M).hom.val
    (homOfLE (le_top : U ≤ ⊤)).op
      (TensorSections.tensorSection (𝟙_ X.Modules) M ⊤ (TensorSections.monoidalUnitSection X) x)
  rw [TensorSections.tensorSection_restrict, GlobalTensorSectionCoherence.leftUnitor_tensorSection_top] at h
  exact h

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictedUnitTensorSection
