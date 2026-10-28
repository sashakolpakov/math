import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityPower
import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientCoordinatesFiltration

/-! # Weak Admissibility Coefficient Extension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityCoefficientExtension

noncomputable section

/-! Finite coefficient extension preserves degree-one weak admissibility over the rational base field. -/

open scoped TensorProduct

variable {q : ℕ} [Fact q.Prime]
  {V : Type*} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]

theorem weaklyAdmissible_coefficient_h1
    (L : Type*) [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    (F : Linear.FiniteFiltration ℚ_[q] V) (φ : V ≃ₗ[ℚ_[q]] V)
    (hF : Linear.WeaklyAdmissible q F φ) (hF0 : F.step 0 = ⊤) (hF2 : F.step 2 = ⊥) :
    Linear.WeaklyAdmissible q (Linear.restrictScalarFiltration L (Linear.finiteCoefficientFiltration L F))
      ((φ.baseChange ℚ_[q] L V V).restrictScalars ℚ_[q]) := by
  let b := Module.finBasis ℚ_[q] L
  let e : (L ⊗[ℚ_[q]] V) ≃ₗ[ℚ_[q]] (Fin (Module.finrank ℚ_[q] L) → V) :=
    TensorCoordinates.CoefficientCoordinates.equiv b
  apply WeakAdmissibilityEquiv.weaklyAdmissible_equiv e.symm (PowerFiltration.FiltrationTransport.power _ F) _
    (LinearEquiv.piCongrRight (fun _ => φ))
  · intro i
    exact (Submodule.map_symm_eq_iff e).mpr (CoefficientCoordinatesFiltration.CoefficientCoordinates.filtration b F i)
  · intro x
    apply e.injective
    rw [e.apply_symm_apply]
    change (fun i => φ (x i)) = e (φ.toLinearMap.baseChange L (e.symm x))
    rw [TensorCoordinates.CoefficientCoordinates.naturality]
    simp only [e, LinearEquiv.apply_symm_apply]
    rfl
  · exact WeakAdmissibilityPower.weaklyAdmissible_power_h1 F φ hF hF0 hF2 _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityCoefficientExtension
