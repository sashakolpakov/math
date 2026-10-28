import OAI.NumberTheory.PadicHodge.GeometricComparison.FiltrationTransportT

/-! # Weak Admissibility Transport -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityTransport.FiltrationTransport

noncomputable section

/-! Weak admissibility is preserved by the actual transported filtration and conjugate Frobenius. -/

universe u v w
variable {R : Type u} [Field R]
  {D : Type v} [AddCommGroup D] [Module R D]
  {E : Type w} [AddCommGroup E] [Module R E]

def conjugateEquiv (e : D ≃ₗ[R] E) (φ : D ≃ₗ[R] D) : E ≃ₗ[R] E :=
  e.symm.trans (φ.trans e)

theorem conjugateEquiv_apply (e : D ≃ₗ[R] E) (φ : D ≃ₗ[R] D) (x : E) :
    conjugateEquiv e φ x = e (φ (e.symm x)) := rfl

theorem conjugateEquiv_toLinearMap (e : D ≃ₗ[R] E) (φ : D ≃ₗ[R] D) :
    (conjugateEquiv e φ).toLinearMap = e.conj φ.toLinearMap := rfl

theorem det_eq_of_intertwines (e : D ≃ₗ[R] E) (T : Module.End R D) (U : Module.End R E)
    (h : ∀ x, e (T x) = U (e x)) : U.det = T.det := by
  have he : U = e.conj T := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] using (h x).symm
  rw [he]
  exact LinearMap.det_conj T e

theorem comap_stable (e : D ≃ₗ[R] E) (φ : D ≃ₗ[R] D) (T : Submodule R E)
    (hT : T ≤ T.comap (conjugateEquiv e φ).toLinearMap) :
    T.comap e.toLinearMap ≤ (T.comap e.toLinearMap).comap φ.toLinearMap := by
  intro x hx
  have h := hT hx
  change e (φ (e.symm (e x))) ∈ T at h
  change e (φ x) ∈ T
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem restrict_det_eq (e : D ≃ₗ[R] E) (φ : D ≃ₗ[R] D) (T : Submodule R E)
    (hT : T ≤ T.comap (conjugateEquiv e φ).toLinearMap) :
    ((conjugateEquiv e φ).toLinearMap.restrict hT).det =
      (φ.toLinearMap.restrict (comap_stable e φ T hT)).det := by
  let eT := e.ofSubmodule' T
  apply det_eq_of_intertwines eT
  intro x
  apply Subtype.ext
  change e (φ (x : D)) = e (φ (e.symm (e (x : D))))
  rw [LinearEquiv.symm_apply_apply]

variable (q : ℕ) [Fact q.Prime]
  {V : Type v} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]
  {W : Type w} [AddCommGroup W] [Module ℚ_[q] W] [FiniteDimensional ℚ_[q] W]

/-- The numerical assertion transfers through the comparison; every stable subspace is tested. -/
theorem weaklyAdmissible_map (e : V ≃ₗ[ℚ_[q]] W) (F : Linear.FiniteFiltration ℚ_[q] V)
    (φ : V ≃ₗ[ℚ_[q]] V) (h : Linear.WeaklyAdmissible q F φ) :
    Linear.WeaklyAdmissible q (FiltrationTransportT.FiltrationTransport.map e F) (conjugateEquiv e φ) := by
  constructor
  · rw [FiltrationTransportT.FiltrationTransport.tH_map, conjugateEquiv_toLinearMap]
    change F.tH = (Padic.valuation (LinearMap.det
      (e.toLinearMap.comp (φ.toLinearMap.comp e.symm.toLinearMap))) : ℚ)
    rw [LinearMap.det_conj]
    exact h.1
  · intro T hT
    let S := T.comap e.toLinearMap
    have hS : S ≤ S.comap φ.toLinearMap := comap_stable e φ T hT
    have hmap : S.map e.toLinearMap = T := Submodule.map_comap_eq_of_surjective e.surjective T
    have hH : ((FiltrationTransportT.FiltrationTransport.map e F).restrict T).tH = (F.restrict S).tH := by
      rw [← hmap]
      exact FiltrationTransportT.FiltrationTransport.tH_restrict_map e F S
    rw [hH, restrict_det_eq]
    exact h.2 S hS

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityTransport.FiltrationTransport
