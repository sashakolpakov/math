import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePhaseProjection
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice

/-! # Scalar Phase -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.ScalarPhase.Realization

noncomputable section

/-! The paired scalar's finite momentum-position convention agrees with the local Levi action. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable (q : ℕ) [Fact q.Prime]

theorem scalarGL_matrix (a : ℚ_[q]ˣ) :
    (LocalLiftChoice.Realization.scalarGL q a).val = Matrix.diagonal (fun _ : Fin 3 => (a : ℚ_[q])) := rfl

theorem scalarGL_inverse_matrix (a : ℚ_[q]ˣ) :
    ((LocalLiftChoice.Realization.scalarGL q a)⁻¹).val = Matrix.diagonal (fun _ : Fin 3 => (a : ℚ_[q])⁻¹) := by
  change ((Matrix.GeneralLinearGroup.scalar (Fin 3) a)⁻¹).val = _
  rw [← map_inv]
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_inv_eq_inv_val]

theorem scalar_levi_phase (a : ℚ_[q]ˣ) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) :
    Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic (LocalLiftChoice.Realization.scalarGL q a)) v =
      Sum.elim (fun i => (a : ℚ_[q]) * v (Sum.inl i))
        (fun i => (a : ℚ_[q])⁻¹ * v (Sum.inr i)) := by
  unfold Weil.Local.FunctionsMetaplectic.Construction.symplecticAction
  rw [Weil.Local.Generators.Construction.leviSymplectic_matrix, scalarGL_matrix, scalarGL_inverse_matrix, Matrix.diagonal_transpose,
    Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec, zero_add, add_zero]
  funext j
  cases j with
  | inl i => exact Matrix.mulVec_diagonal _ _ i
  | inr i => exact Matrix.mulVec_diagonal _ _ i

def pairedScalarPhase {Place : Type*} (a : Place → ℚ_[q]ˣ)
    (x : Sum (Place × Fin 3) (Place × Fin 3) → ℚ_[q]) : Sum (Place × Fin 3) (Place × Fin 3) → ℚ_[q] :=
  Sum.elim (fun p => (a p.1 : ℚ_[q]) * x (Sum.inl p))
    (fun p => (a p.1 : ℚ_[q])⁻¹ * x (Sum.inr p))

theorem pairedScalarPhase_localBlock {Place : Type*} (μ : Place) (a : Place → ℚ_[q]ˣ)
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) :
    pairedScalarPhase q a (FinitePhaseProjection.Realization.localBlockPhase q μ v) =
      FinitePhaseProjection.Realization.localBlockPhase q μ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.Generators.Construction.leviSymplectic (LocalLiftChoice.Realization.scalarGL q (a μ)⁻¹)) v) := by
  rw [scalar_levi_phase]
  funext j
  cases j with
  | inl p =>
      change (a p.1 : ℚ_[q]) * (if p.1 = μ then v (Sum.inr p.2) else 0) =
        if p.1 = μ then ((a μ)⁻¹ : ℚ_[q]ˣ).val⁻¹ * v (Sum.inr p.2) else 0
      by_cases hp : p.1 = μ <;> simp [hp]
  | inr p =>
      change (a p.1 : ℚ_[q])⁻¹ * (if p.1 = μ then v (Sum.inl p.2) else 0) =
        if p.1 = μ then ((a μ)⁻¹ : ℚ_[q]ˣ).val * v (Sum.inl p.2) else 0
      by_cases hp : p.1 = μ <;> simp [hp]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.ScalarPhase.Realization
