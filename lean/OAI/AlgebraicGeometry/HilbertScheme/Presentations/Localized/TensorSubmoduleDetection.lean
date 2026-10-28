import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.BaseChange

/-! # Tensor Submodule Detection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.TensorSubmoduleDetection

noncomputable section

/-! Submodules are detected by their tensor extensions to all local rings
at maximal ideals, without noetherianity or finite-generation hypotheses. -/

open TensorProduct

universe u v
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem submodule_eq_of_localized_tensor (P Q : Submodule R M)
    (h : ∀ p : Ideal R, ∀ _ : p.IsMaximal,
      P.baseChange (Localization.AtPrime p) = Q.baseChange (Localization.AtPrime p)) : P = Q := by
  apply Submodule.eq_of_localization_maximal
    (fun p _ => Localization.AtPrime p)
    (fun p _ => Localization.AtPrime p ⊗[R] M)
    (fun p _ => TensorProduct.mk R (Localization.AtPrime p) M 1)
  intro p hp
  rw [Submodule.localized'_eq_span, Submodule.localized'_eq_span,
    ← Submodule.map_coe, ← Submodule.map_coe, ← Submodule.baseChange_eq_span,
    ← Submodule.baseChange_eq_span]
  exact h p hp

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.TensorSubmoduleDetection
