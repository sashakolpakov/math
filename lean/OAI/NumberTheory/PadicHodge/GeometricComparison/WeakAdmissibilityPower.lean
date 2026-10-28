import OAI.NumberTheory.PadicHodge.GeometricComparison.PowerFiltration
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityProduct

/-! # Weak Admissibility Power -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityPower

noncomputable section

/-! Finite powers preserve weak admissibility while testing arbitrary stable subspaces. -/

open OAI.NumberTheory.PadicHodge.GeometricComparison.PowerFiltration.FiltrationTransport

variable {q : ℕ} [Fact q.Prime]
  {V : Type*} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]

theorem weaklyAdmissible_subsingleton [Subsingleton V]
    (F : Linear.FiniteFiltration ℚ_[q] V) (φ : V ≃ₗ[ℚ_[q]] V) : Linear.WeaklyAdmissible q F φ := by
  constructor
  · simp [WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.tH, LinearMap.det_eq_one_of_subsingleton,
      Module.finrank_zero_of_subsingleton]
  · intro S hS
    simp [WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.tH, LinearMap.det_eq_one_of_subsingleton,
      Module.finrank_zero_of_subsingleton]

theorem weaklyAdmissible_power_h1
    (F : Linear.FiniteFiltration ℚ_[q] V) (φ : V ≃ₗ[ℚ_[q]] V)
    (hF : Linear.WeaklyAdmissible q F φ) (hF0 : F.step 0 = ⊤) (hF2 : F.step 2 = ⊥) (n : ℕ) :
    Linear.WeaklyAdmissible q (PowerFiltration.FiltrationTransport.power (Fin n) F) (LinearEquiv.piCongrRight (fun _ => φ)) := by
  induction n with
  | zero => exact weaklyAdmissible_subsingleton _ _
  | succ n ih =>
    apply WeakAdmissibilityEquiv.weaklyAdmissible_equiv (PowerFiltration.FiltrationTransport.powerSuccEquiv n).symm
      (ProductFiltration.FiltrationTransport.product F (PowerFiltration.FiltrationTransport.power (Fin n) F)) _ (φ.prodCongr (LinearEquiv.piCongrRight (fun _ => φ)))
    · intro i
      exact (Submodule.map_symm_eq_iff (PowerFiltration.FiltrationTransport.powerSuccEquiv n)).mpr (PowerFiltration.FiltrationTransport.powerSucc_step n F i)
    · intro x
      ext j
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · rfl
    · exact WeakAdmissibilityProduct.weaklyAdmissible_product_h1 F (PowerFiltration.FiltrationTransport.power (Fin n) F) φ _ hF ih hF0 hF2
        (PowerFiltration.FiltrationTransport.power_top _ F 0 hF0) (PowerFiltration.FiltrationTransport.power_bot _ F 2 hF2)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityPower
