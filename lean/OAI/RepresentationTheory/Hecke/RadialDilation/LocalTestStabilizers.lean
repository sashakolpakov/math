import OAI.RepresentationTheory.Hecke.RadialDilation.ContinuousTestFamilies
import OAI.RepresentationTheory.Hecke.RadialDilation.Haar
import OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest
import OAI.RepresentationTheory.Weil.Local.LinearSubstitution

/-! # Local Test Stabilizers -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.LocalTestStabilizers.Realization

noncomputable section

/-! Actual p-adic test functions are fixed by sufficiently small generator parameters. -/

open scoped Classical _root_.Topology _root_.Matrix
open Filter _root_.Matrix OAI.RepresentationTheory.Weil.Local.LinearSubstitution.Construction

variable (q n : ℕ) [Fact q.Prime]

theorem eventually_quadraticOperator_fixed (ψ : AddChar ℚ_[q] ℂ)
    (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (f : Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n → ℂ) (hc : HasCompactSupport f) :
    ∀ᶠ B : Matrix (Fin n) (Fin n) ℚ_[q] in 𝓝 0, Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator ψ B f = f := by
  have hquad : Continuous (fun p : Matrix (Fin n) (Fin n) ℚ_[q] × Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n => Weil.Local.FunctionsMetaplectic.Construction.quadratic p.1 p.2) := by
    unfold Weil.Local.FunctionsMetaplectic.Construction.quadratic
    fun_prop
  have hphase := (Weil.UnitarySplitting.LocalTest.Construction.additiveCharacter_locallyConstant_ultra ψ hψ).comp_continuous hquad
  have hzero (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n) : ψ (Weil.Local.FunctionsMetaplectic.Construction.quadratic (0 : Matrix (Fin n) (Fin n) ℚ_[q]) x) = 1 := by
    simp [Weil.Local.FunctionsMetaplectic.Construction.quadratic]
  filter_upwards [ContinuousTestFamilies.Realization.eventually_compact_phase_one 0 _ hphase hzero (tsupport f) hc] with B hB
  funext x
  rw [Weil.Local.FunctionsMetaplectic.Construction.quadraticOperator_apply]
  by_cases hx : f x = 0
  · rw [hx, mul_zero]
  · have hBx : ψ (Weil.Local.FunctionsMetaplectic.Construction.quadratic B x) = 1 := hB x (subset_tsupport f hx)
    rw [hBx, one_mul]

theorem eventually_substitutionOperator_fixed
    (f : Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n → ℂ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∀ᶠ A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n in 𝓝 1, Weil.Local.FunctionsMetaplectic.Construction.substitutionOperator A f = f := by
  let e : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n → Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n ≃ₜ Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n :=
    fun A => (Weil.Local.LinearSubstitution.Construction.positionAddEquiv A⁻¹).toHomeomorph
  have he₀ : e 1 = Homeomorph.refl _ := by
    apply Homeomorph.ext
    intro x
    change (↑((1 : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n)⁻¹) : Matrix (Fin n) (Fin n) ℚ_[q]) *ᵥ x = x
    simp
  have he : Continuous (fun p : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n × Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n => e p.1 p.2) := by
    change Continuous (fun p : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n × Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n =>
      (↑(p.1⁻¹) : Matrix (Fin n) (Fin n) ℚ_[q]) *ᵥ p.2)
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hi : Continuous (fun p : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n × Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n => (e p.1).symm p.2) := by
    change Continuous (fun p : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n × Weil.Local.FunctionsMetaplectic.Construction.Position ℚ_[q] n =>
      (↑((p.1⁻¹)⁻¹) : Matrix (Fin n) (Fin n) ℚ_[q]) *ᵥ p.2)
    unfold Matrix.mulVec dotProduct
    fun_prop
  filter_upwards [ContinuousTestFamilies.Realization.eventually_homeomorph_test_fixed 1 e he₀ he hi f hf hc] with A hA
  funext x
  exact hA x

theorem eventually_determinant_norm_one :
    ∀ᶠ A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n in 𝓝 1, ‖(Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] A).val‖ = 1 := by
  have hcont : Continuous (fun A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n => ‖A.val.det - 1‖) := by fun_prop
  have hn : ∀ᶠ A : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n in 𝓝 1, ‖A.val.det - 1‖ < 1 :=
    (isOpen_lt hcont continuous_const).mem_nhds (by simp)
  filter_upwards [hn] with A hA
  have he := Padic.norm_eq_of_norm_sub_lt_right (z1 := A.val.det) (z2 := (1 : ℚ_[q]))
    (by simpa only [norm_one] using hA)
  exact he.trans (norm_one : ‖(1 : ℚ_[q])‖ = 1)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.LocalTestStabilizers.Realization
