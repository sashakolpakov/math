import OAI.NumberTheory.PadicHodge.GeometricComparison.NestedFiltration
import OAI.NumberTheory.PadicHodge.GeometricComparison.SplitFiltration
import OAI.NumberTheory.PadicHodge.GeometricComparison.SplitDeterminant

/-! # Weak Admissibility Split -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilitySplit

noncomputable section

/-! A Frobenius invariant summand that splits the filtration is weakly admissible. -/

variable {q : ℕ} [Fact q.Prime]
  {V : Type*} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]

theorem weaklyAdmissible_split (F : Linear.FiniteFiltration ℚ_[q] V)
    (φ : V ≃ₗ[ℚ_[q]] V) (h : Linear.WeaklyAdmissible q F φ)
    (S T : Submodule ℚ_[q] V) (hc : IsCompl S T)
    (hS : S ≤ S.comap φ.toLinearMap) (hT : T ≤ T.comap φ.toLinearMap)
    (hsplit : ∀ i, (S ⊓ F.step i) ⊔ (T ⊓ F.step i) = F.step i)
    (ψ : S ≃ₗ[ℚ_[q]] S) (hψ : ψ.toLinearMap = φ.toLinearMap.restrict hS) :
    Linear.WeaklyAdmissible q (F.restrict S) ψ := by
  apply (NestedFiltration.weaklyAdmissible_restrict_iff F φ h S hS ψ hψ).mpr
  rw [hψ]
  have hs := h.2 S hS
  have ht := h.2 T hT
  have hH := SplitFiltration.FiltrationTransport.split_tH F S T hc.disjoint hsplit
  have hN := SplitDeterminant.FiltrationTransport.split_newton φ S T hc hS hT
  have he := h.1
  linarith

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilitySplit
