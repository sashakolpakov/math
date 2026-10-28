import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityTransport

/-! # Weak Admissibility Equiv -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityEquiv

noncomputable section

/-! Transfer of weak admissibility along actual filtered intertwining equivalences. -/

namespace FiltrationTransport

theorem ext {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (F G : Linear.FiniteFiltration K V) (h : ∀ i, F.step i = G.step i) : F = G := by
  cases F
  cases G
  congr
  exact funext h

end FiltrationTransport

variable {q : ℕ} [Fact q.Prime]
  {V W : Type*} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]
  [AddCommGroup W] [Module ℚ_[q] W] [FiniteDimensional ℚ_[q] W]

theorem weaklyAdmissible_equiv (e : V ≃ₗ[ℚ_[q]] W)
    (F : Linear.FiniteFiltration ℚ_[q] V) (G : Linear.FiniteFiltration ℚ_[q] W)
    (φ : V ≃ₗ[ℚ_[q]] V) (ψ : W ≃ₗ[ℚ_[q]] W)
    (hFil : ∀ i, (F.step i).map e.toLinearMap = G.step i)
    (hφ : ∀ x, e (φ x) = ψ (e x)) (h : Linear.WeaklyAdmissible q F φ) :
    Linear.WeaklyAdmissible q G ψ := by
  have hG : FiltrationTransportT.FiltrationTransport.map e F = G := FiltrationTransport.ext _ _ hFil
  have hψ : WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv e φ = ψ := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv_apply, LinearEquiv.symm_apply_apply] using hφ x
  simpa only [hG, hψ] using WeakAdmissibilityTransport.FiltrationTransport.weaklyAdmissible_map q e F φ h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityEquiv
