import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerRows
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechSelectedComplement

/-! # Selected Support -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal

noncomputable section

/-! The local support conditions also describe the selected complement
itself. The canonical selected extension is its genuine support-forgetting
map on the original single quasicoherent sheaf. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{0}} {C : Type} [Preorder C] [HasFiniteProducts C]
  {G₁ G₂ : C ⥤ X.Opens} {ι : Type} [LinearOrder ι] {W : ι → C} {O₁ O₂ : X.Opens}
  (H : InjectiveIntegerRows.SingleSupportedCandidate.Conditions G₁ G₂ W O₁ O₂)

include H in
omit [LinearOrder ι] in
theorem InjectiveIntegerRows.SingleSupportedCandidate.Conditions.selected : InjectiveIntegerRows.SingleSupportedCandidate.Conditions G₂ G₂ W O₂ O₂ where
  outside_le := le_rfl
  intersection_eq := rfl
  local_global := H.local_global
  wide_global := H.local_global
  wide_punctured := fun j => (H.local_punctured j).trans H.outside_le
  local_punctured := fun j => (H.local_punctured j).trans H.outside_le
  wide_cover := H.intersection_eq ▸ H.local_cover
  local_cover := H.intersection_eq ▸ H.local_cover
  wide_affine := H.local_affine
  local_affine := H.local_affine

variable
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G₁]
  [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G₂]
  (N : X.Modules) (c : ℕ)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InjectiveIntegerCoordinates

omit [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G₁] in
theorem InjectiveIntegerRows.SingleSupportedCandidate.Conditions.moduleSelectedExtension_eq (q : ℕ) :
    H.moduleSelectedExtension N c q = H.selected.moduleForget N c q :=
  Supported.CechSelectedComplement.forgetSupport ℤ X G₂ W O₁ O₂ H.intersection_eq
    H.local_global (InjectiveIntegerCoordinates.complex N c) H.local_punctured H.selected.wide_punctured
    H.local_cover H.selected.wide_cover
    (InjectiveIntegerRows.exactAt_succ G₂ W N c) q

variable [N.IsQuasicoherent]

omit [∀ (n : ℕ) (a : Fin (n+1) → ι), PreservesLimit (Discrete.functor (W ∘ a)) G₁] in
theorem InjectiveIntegerRows.SingleSupportedCandidate.Conditions.selectedExtension_eq (q : ℕ) :
    H.selectedExtension N c q = H.selected.forgetSupport N c q := by
  dsimp only [InjectiveIntegerRows.SingleSupportedCandidate.Conditions.selectedExtension, InjectiveIntegerRows.SingleSupportedCandidate.Conditions.forgetSupport]
  rw [H.moduleSelectedExtension_eq N c q]

theorem InjectiveIntegerRows.SingleSupportedCandidate.Conditions.candidate_selected (q : ℕ) :
    H.candidate N c q ≫ H.forgetSupport N c q = H.selected.forgetSupport N c q :=
  (H.candidate_global N c q).trans (H.selectedExtension_eq N c q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal
