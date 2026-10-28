import OAI.Analysis.PDE.Weak.Boundary.NormalFlux

/-! Dividing a weak scalar flux by a smooth nowhere-zero coefficient.
This is the final algebraic step in normal-derivative recovery. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem weak_division_identity
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (w : OAI.Analysis.PDE.Variational.CellCoordinates m)
    (a u v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (ha : ContDiff ℝ ∞ a) (hane : ∀ x, a x ≠ 0)
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (hprod : ∀ φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, v x * φ x) = -(∫ x, (a x * u x) * fderiv ℝ φ x w)) :
    ∀ φ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, ((v x - fderiv ℝ a x w * u x) / a x) * φ x) =
        -(∫ x, u x * fderiv ℝ φ x w) := by
  intro φ hφ hs hφΩ
  let ψ : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ := fun x => φ x / a x
  have hψ : ContDiff ℝ ∞ ψ := hφ.div ha hane
  have hsψ : HasCompactSupport ψ := by
    change HasCompactSupport (fun x => φ x * (a x)⁻¹)
    exact hs.mul_right
  have hψΩ : tsupport ψ ⊆ Ω := by
    apply Subset.trans (b := tsupport φ) _ hφΩ
    change tsupport (fun x => φ x * (a x)⁻¹) ⊆ tsupport φ
    exact tsupport_mul_subset_left
  have haψ : (fun x => a x * ψ x) = φ := by
    funext x
    dsimp [ψ]
    field_simp [hane x]
  have hD (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      fderiv ℝ φ x w = fderiv ℝ a x w * ψ x + a x * fderiv ℝ ψ x w := by
    have h := ((ha.differentiable (by simp) x).hasFDerivAt.mul
      (hψ.differentiable (by simp) x).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => a y * ψ y) x = _ at h
    rw [haψ] at h
    have hh := congrArg (fun L => L w) h
    simpa only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul, add_comm, mul_comm] using hh
  have hflux (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      (a x * u x) * fderiv ℝ ψ x w =
        u x * fderiv ℝ φ x w - u x * (fderiv ℝ a x w * ψ x) := by
    rw [hD]
    ring
  have htest : ContDiff ℝ ∞ (fun x => fderiv ℝ a x w * ψ x) :=
    (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative ha (by simp) w).mul hψ
  have hstest : HasCompactSupport (fun x => fderiv ℝ a x w * ψ x) := hsψ.mul_left
  have hi1 : Integrable (fun x => u x * fderiv ℝ φ x w) :=
    hu.integrable_mul ((OAI.Analysis.PDE.Green.continuous_directional (hφ.of_le (by simp)) w).memLp_of_hasCompactSupport (p := 2)
      (hs.fderiv_apply ℝ w))
  have hi2 : Integrable (fun x => u x * (fderiv ℝ a x w * ψ x)) :=
    hu.integrable_mul (htest.continuous.memLp_of_hasCompactSupport (p := 2) hstest)
  have hi3 : Integrable (fun x => v x * ψ x) :=
    hv.integrable_mul (hψ.continuous.memLp_of_hasCompactSupport (p := 2) hsψ)
  have he := hprod ψ hψ hsψ hψΩ
  simp_rw [hflux] at he
  rw [integral_sub hi1 hi2] at he
  have hleft (x : OAI.Analysis.PDE.Variational.CellCoordinates m) :
      ((v x - fderiv ℝ a x w * u x) / a x) * φ x =
        v x * ψ x - u x * (fderiv ℝ a x w * ψ x) := by
    dsimp [ψ]
    ring
  simp_rw [hleft]
  rw [integral_sub hi3 hi2]
  linarith

end OAI.Analysis.PDE.Weak
