import OAI.Analysis.PDE.Weak.Boundary.Weak.Scalar

/-! Recovering a genuine L² normal derivative by the divergence equation,
the known off-diagonal derivative, and the positive normal coefficient. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem normal_recovery_formula
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω)
    {H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m} {f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ}
    (hweak : WeakDivergenceEquation Ω H f) (hH : MemLp H 2 volume) (hf : MemLp f 2 volume)
    (k : Fin (m + 1)) (t : Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (ht : ∀ i, MemLp (t i) 2 volume)
    (hpartial : ∀ i, i ≠ k → HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1)
      (fun x => H x i) (t i))
    (a u K v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (ha : ContDiff ℝ ∞ a) (hane : ∀ x, a x ≠ 0)
    (hu : MemLp u 2 volume) (hK : MemLp K 2 volume) (hv : MemLp v 2 volume)
    (hDK : HasWeakDirectionalDerivativeOn volume Ω (Pi.single k 1) K v)
    (hdecomp : ∀ x, H x k = a x * u x + K x)
    {M N : ℝ} (hDa : ∀ x, ‖fderiv ℝ a x (Pi.single k 1)‖ ≤ M)
    (hInv : ∀ x, ‖(a x)⁻¹‖ ≤ N) :
    let g := fun x => (-f x - ∑ i ∈ Finset.univ.erase k, t i x -
      v x - fderiv ℝ a x (Pi.single k 1) * u x) / a x
    MemLp g 2 volume ∧
      HasWeakDirectionalDerivativeOn volume Ω (Pi.single k 1) u g := by
  let q : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ := fun x => -f x - ∑ i ∈ Finset.univ.erase k, t i x
  obtain ⟨hq, hqweak⟩ := hweak.normal_flux_derivative hH hf k t ht (by
    intro i hi φ hφ hs hsub
    exact (hpartial i hi).scalar_identity volume φ (hφ.of_le (by simp)) hs hsub)
  have hDq : HasWeakDirectionalDerivativeOn volume Ω (Pi.single k 1) (fun x => H x k) q :=
    hasWeakDirectionalDerivativeOn_of_smooth volume hΩ _ _ (memLp_cell_component hH k) hq _ hqweak
  have hsub := hDq.scalar_sub volume (memLp_cell_component hH k) hK hq hv hDK
  have hau : HasWeakDirectionalDerivativeOn volume Ω (Pi.single k 1)
      (fun x => a x * u x) (fun x => q x - v x) := by
    apply hsub.congr_on volume
    · filter_upwards with x
      intro _
      rw [hdecomp]
      ring
    · filter_upwards with x
      intro _
      rfl
  let g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ := fun x =>
    (q x - v x - fderiv ℝ a x (Pi.single k 1) * u x) / a x
  have hDac : Continuous (fun x => fderiv ℝ a x (Pi.single k 1)) :=
    ((ha.of_le (by simp) : ContDiff ℝ 1 a).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hnum : MemLp (fun x => q x - v x - fderiv ℝ a x (Pi.single k 1) * u x) 2 volume :=
    (hq.sub hv).sub (memLp_bounded_scalar_mul volume hDac hu hDa)
  have hg : MemLp g 2 volume := by
    have h := memLp_bounded_scalar_mul volume (ha.continuous.inv₀ hane) hnum hInv
    simpa only [g, div_eq_mul_inv, Pi.inv_apply, mul_comm] using h
  refine ⟨hg, ?_⟩
  apply hasWeakDirectionalDerivativeOn_of_smooth volume hΩ u g hu hg
  exact weak_division_identity (Pi.single k 1) a u (fun x => q x - v x) ha hane hu (hq.sub hv)
    (fun φ hφ hs hsub => hau.scalar_identity volume φ (hφ.of_le (by simp)) hs hsub)

end OAI.Analysis.PDE.Weak
