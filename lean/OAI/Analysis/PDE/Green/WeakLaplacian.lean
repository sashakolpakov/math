import OAI.Analysis.PDE.Green.TimeTest

/-! Weak extended-time Laplacian identity for the determinant energy density. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

def spatialPencilEnergyDensity {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s) : ℝ :=
  u x * ∫ t in (0 : ℝ)..1, OAI.LinearAlgebra.Moore.mooreDet n
    ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x).submatrix Fin.succ Fin.succ)

/-- The determinant energy has the asserted weak time-Laplacian, before
disintegration into moving fibers. All integrations by parts are derived. -/
theorem determinant_energy_weak_time_laplacian {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    {r u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B)
    (hη : ContDiff ℝ 3 η) (hb : Bornology.IsBounded {x | r x < 0})
    (hrne : ∀ x ∈ closure {x | r x < 0}, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin (n + 1) → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0)
    (hspatial : ∀ x, r x < 0 → ∀ t ∈ Icc (0 : ℝ) 1,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x).submatrix
        Fin.succ Fin.succ)).PosSemidef) :
    (∫ x in {x | r x < 0}, Laplacian.laplacian η (timeProjection n s x) *
      spatialPencilEnergyDensity e B u x) =
    ∫ x in {x | r x < 0}, η (timeProjection n s x) *
      (OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
  have htest : ContDiff ℝ 3 (fun y => η (timeProjection n s y)) :=
    hη.comp (timeProjection n s).contDiff
  have hv := determinant_pencil_energy_variation e hr hu hB htest hb hrne huz hcommon
  rw [← hv]
  apply setIntegral_congr_fun (isOpen_lt hr.continuous continuous_const).measurableSet
  intro x hx
  dsimp only
  unfold spatialPencilEnergyDensity
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
  have hp : ContDiff ℝ 2 (fun y => B y + t * u y) :=
    (hB.of_le (by norm_num)).add (contDiff_const.mul (hu.of_le (by norm_num)))
  dsimp only
  rw [mooreDifferential_time_test e he (hη.of_le (by norm_num)) _
    (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hp.contDiffAt) (hspatial x hx t ht')]
  ring

end OAI.Analysis.PDE.Green
