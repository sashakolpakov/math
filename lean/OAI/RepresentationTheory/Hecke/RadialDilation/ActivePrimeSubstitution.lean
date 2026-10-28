import OAI.RepresentationTheory.Hecke.RadialDilation.DiagonalUnits
import OAI.RepresentationTheory.Hecke.RadialDilation.IndexedPrimeSubstitution
import OAI.RepresentationTheory.Hecke.RadialDilation.CanonicalVacuumTensor

/-! # Active Prime Substitution -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.ActivePrimeSubstitution.Realization

noncomputable section

/-! A diagonal full-prime substitution changes precisely the selected radial coordinates. -/

open scoped Classical _root_.Matrix

theorem selected_coordinate_substitution {A B : Type*} [AddCommGroup A] [Ring B]
    (I : B →+ A) (c : Prop) [Decidable c] (a y : B) (x : A) :
    I ((if c then a else 1) * y) + (x - I y) =
      (if c then I (a * y) else 0) + (x - (if c then I y else 0)) := by
  by_cases hc : c
  · simp only [hc, ite_true]
  · simp only [hc, ite_false, one_mul, zero_add, sub_zero]
    abel

variable (q : ℕ) [Fact q.Prime] {Place : Type*} [Fintype Place] [DecidableEq Place]
  {n : ℕ} (e : (Place × Fin 3) ≃ Fin n) (μ : Place)

def activePrimeGL (a : ℚ_[q]ˣ) : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear ℚ_[q] n :=
  DiagonalUnits.Realization.diagonalUnitMatrix (fun i => DiagonalUnits.Realization.activeCoordinateUnits μ a (e.symm i))

theorem activePrimeGL_determinant (a : ℚ_[q]ˣ) :
    Weil.Local.FunctionsMetaplectic.Construction.determinantUnit ℚ_[q] (activePrimeGL q e μ a) = a ^ 3 := by
  change Matrix.GeneralLinearGroup.det (DiagonalUnits.Realization.diagonalUnitMatrix _) = _
  rw [DiagonalUnits.Realization.diagonalUnitMatrix_det, DiagonalUnits.Realization.reindexed_activeCoordinateUnits_prod]

omit [Fintype Place] in
theorem activePrimeGL_inverse_substitution (a : ℚ_[q]ˣ) (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (IndexedPrimeChart.Realization.indexedPrimeChart q e).symm
      ((activePrimeGL q e μ a)⁻¹.val *ᵥ IndexedPrimeChart.Realization.indexedPrimeProjection q e x, PrimeChart.Realization.fullPrimeAway q x) =
    (FiniteBlockChart.Realization.finiteBlockChart q μ).symm
      ((fun i => (a : ℚ_[q])⁻¹ * FiniteBlockChart.Realization.finiteBlockProjection q μ x i), (FiniteBlockChart.Realization.finiteBlockChart q μ x).2) := by
  change PrimeChart.Realization.fullPrimeInclusion q (fun i =>
      ((activePrimeGL q e μ a)⁻¹.val *ᵥ IndexedPrimeChart.Realization.indexedPrimeProjection q e x) (e i)) +
      (PrimeChart.Realization.fullPrimeAway q x).val = _
  rw [show activePrimeGL q e μ a = DiagonalUnits.Realization.diagonalUnitMatrix
    (fun i => DiagonalUnits.Realization.activeCoordinateUnits μ a (e.symm i)) from rfl,
    DiagonalUnits.Realization.diagonalUnitMatrix_inverse_action, PrimeChart.Realization.fullPrimeAway_val, FiniteBlockChart.Realization.finiteBlockChart_symm]
  funext i
  change FiniteSchur.Realization.finitePadicInclusion q
    (((DiagonalUnits.Realization.activeCoordinateUnits μ a (e.symm (e i)))⁻¹ : ℚ_[q]ˣ).val *
      FiniteSchur.Realization.finitePadicProjection q (x (e.symm (e i)))) +
      (x i - FiniteSchur.Realization.finitePadicInclusion q (FiniteSchur.Realization.finitePadicProjection q (x i))) =
    FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun j => (a : ℚ_[q])⁻¹ * FiniteBlockChart.Realization.finiteBlockProjection q μ x j) i +
      (x i - FiniteBlockChart.Realization.finiteBlockInclusion q μ (FiniteBlockChart.Realization.finiteBlockProjection q μ x) i)
  simp only [Equiv.symm_apply_apply, FiniteBlockChart.Realization.finiteBlockInclusion_apply, CanonicalVacuumTensor.Realization.finiteBlockProjection_apply]
  by_cases hi : i.1 = μ
  · simp only [DiagonalUnits.Realization.activeCoordinateUnits, hi, ite_true, Units.val_inv_eq_inv_val]
    rw [← hi]
  · simp only [DiagonalUnits.Realization.activeCoordinateUnits, hi, ite_false, inv_one, Units.val_one, one_mul,
      zero_add, sub_zero]
    abel

omit [DecidableEq Place] in
theorem canonical_radial_block_substitution (a : ℚ_[q]ˣ) (M : ℕ)
    (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ))) (b : Cm.radialInput q)
    (x : Place × Fin 3 → Theta.PoissonAutomorphyNormalizationData.AQf) :
    (((Real.sqrt (‖(a : ℚ_[q])‖ ^ 3))⁻¹ : ℝ) : ℂ) *
      (Canonical.Realization.canonicalFiniteRadialEmbedding q μ b).val ((FiniteBlockChart.Realization.finiteBlockChart q μ).symm
        ((fun i => (a : ℚ_[q])⁻¹ * FiniteBlockChart.Realization.finiteBlockProjection q μ x i), (FiniteBlockChart.Realization.finiteBlockChart q μ x).2)) =
    (Canonical.Realization.canonicalFiniteRadialEmbedding q μ
      (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b)).val x := by
  change _ * (b.val ((FiniteBlockChart.Realization.finiteBlockChart q μ ((FiniteBlockChart.Realization.finiteBlockChart q μ).symm _)).1) *
      (Canonical.Realization.finiteAwayVacuum q μ).val ((FiniteBlockChart.Realization.finiteBlockChart q μ ((FiniteBlockChart.Realization.finiteBlockChart q μ).symm _)).2)) = _
  rw [Homeomorph.apply_symm_apply]
  change _ * (b.val (fun i => (a : ℚ_[q])⁻¹ * FiniteBlockChart.Realization.finiteBlockProjection q μ x i) *
      (Canonical.Realization.finiteAwayVacuum q μ).val (FiniteBlockChart.Realization.finiteBlockChart q μ x).2) =
    (_ * b.val (fun i => (a : ℚ_[q])⁻¹ * FiniteBlockChart.Realization.finiteBlockProjection q μ x i)) *
      (Canonical.Realization.finiteAwayVacuum q μ).val (FiniteBlockChart.Realization.finiteBlockChart q μ x).2
  rw [Complex.ofReal_inv]
  ring

end

end OAI.RepresentationTheory.Hecke.RadialDilation.ActivePrimeSubstitution.Realization
