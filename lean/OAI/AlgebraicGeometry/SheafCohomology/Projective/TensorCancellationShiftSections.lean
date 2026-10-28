import OAI.AlgebraicGeometry.SheafCohomology.Projective.LocalTensorSectionCoherence

/-! # Tensor Cancellation Shift Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorCancellationShiftSections

noncomputable section

/-! Section-level action of a tensor shift defined by a cancellation isomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
local instance tensorCancellationShiftMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

def tensorCancellationShiftIso {X : Scheme.{u}} {L M N Q : X.Modules}
    (d : Q ≅ M ⊗ N) (e : L ⊗ M ≅ 𝟙_ X.Modules) : L ⊗ Q ≅ N :=
  (Iso.refl L ⊗ᵢ d) ≪≫ (α_ L M N).symm ≪≫ (e ⊗ᵢ Iso.refl N) ≪≫ λ_ N

theorem tensorCancellationShiftIso_tensorSection {X : Scheme.{u}} {L M N Q : X.Modules}
    (d : Q ≅ M ⊗ N) (e : L ⊗ M ≅ 𝟙_ X.Modules) (U : X.Opens)
    (l : Γ(L, U)) (x : Γ(M, U)) (y : Γ(N, U)) (q : Γ(Q, U))
    (hd : d.hom.val.app (op U) q = TensorSections.tensorSection M N U x y) :
    (tensorCancellationShiftIso d e).hom.val.app (op U) (TensorSections.tensorSection L Q U l q) =
      (λ_ N).hom.val.app (op U)
        (TensorSections.tensorSection (𝟙_ X.Modules) N U
          (e.hom.val.app (op U) (TensorSections.tensorSection L M U l x)) y) := by
  change (λ_ N).hom.val.app (op U)
    ((e.hom ⊗ₘ 𝟙 N).val.app (op U)
      ((α_ L M N).inv.val.app (op U)
        ((𝟙 L ⊗ₘ d.hom).val.app (op U) (TensorSections.tensorSection L Q U l q)))) = _
  rw [TensorFrameSections.tensorSection_map]
  change (λ_ N).hom.val.app (op U)
    ((e.hom ⊗ₘ 𝟙 N).val.app (op U)
      ((α_ L M N).inv.val.app (op U)
        (TensorSections.tensorSection L (M ⊗ N) U l (d.hom.val.app (op U) q)))) = _
  rw [hd, LocalTensorSectionCoherence.associator_inv_tensorSection, TensorFrameSections.tensorSection_map]
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorCancellationShiftSections
