import OAI.Analysis.PDE.Concentration.Lattice.LocalPencil
import OAI.Analysis.PDE.Green.Localized.Laplacian

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix _root_.MeasureTheory OAI.Analysis.PDE.Green OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Topology Matrix.Norms.Elementwise MatrixOrder ComplexOrder

theorem determinant_energy_weak_time_laplacian_lattice_localized {n s m : ℕ}
    (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (c : (Fin (n + 1) × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B)
    (hη : ContDiff ℝ 3 η)
    (hreg : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ (fun y => η (OAI.Analysis.PDE.Green.timeProjection n s y)) =ᶠ[𝓝 x] (fun _ => 0))
    (hboundary : ∀ x, r x = 0 →
      ((∀ᶠ y in 𝓝 x, r y = 0 → u y = 0) ∧
        ∃ w : Fin (n + 1) → Quaternion ℝ, w ≠ 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧
          OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧ star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0) ∨
      (fun y => η (OAI.Analysis.PDE.Green.timeProjection n s y)) =ᶠ[𝓝 x] (fun _ => 0))
    (hspatial : ∀ x ∈ (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      Laplacian.laplacian η (OAI.Analysis.PDE.Green.timeProjection n s x) ≠ 0 → ∀ t ∈ Icc (0 : ℝ) 1,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x).submatrix
        Fin.succ Fin.succ)).PosSemidef)
    (hface : ∀ t : ℝ, CompatibleLatticeFaces c L a b r (OAI.Analysis.PDE.Green.secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor (n + 1)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u
      (fun x => η (OAI.Analysis.PDE.Green.timeProjection n s x)))) :
    (∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      Laplacian.laplacian η (OAI.Analysis.PDE.Green.timeProjection n s x) * OAI.Analysis.PDE.Green.spatialPencilEnergyDensity e B u x) =
    ∫ x in (euclideanLatticeCell c L a b) ∩ {x | r x < 0},
      η (OAI.Analysis.PDE.Green.timeProjection n s x) *
      (OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
  have htest : ContDiff ℝ 3 (fun y => η (OAI.Analysis.PDE.Green.timeProjection n s y)) :=
    hη.comp (OAI.Analysis.PDE.Green.timeProjection n s).contDiff
  have hv := determinant_pencil_variation_lattice_localized e c L a b hab hr hu hB htest
    hreg hboundary hface
  rw [← hv]
  apply setIntegral_congr_fun ((measurableSet_euclideanLatticeCell c L a b).inter
    (isOpen_lt hr.continuous continuous_const).measurableSet)
  intro x hx
  dsimp only
  unfold OAI.Analysis.PDE.Green.spatialPencilEnergyDensity
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
  have hp : ContDiff ℝ 2 (fun y => B y + t * u y) :=
    (hB.of_le (by norm_num)).add (contDiff_const.mul (hu.of_le (by norm_num)))
  dsimp only
  by_cases hΔ : Laplacian.laplacian η (OAI.Analysis.PDE.Green.timeProjection n s x) = 0
  · rw [OAI.Analysis.PDE.Green.quaternionHessian_time_only e he (hη.of_le (by norm_num)), hΔ, zero_smul,
      OAI.Analysis.PDE.Green.mooreDifferential_zero_direction]
    ring
  · rw [OAI.Analysis.PDE.Green.mooreDifferential_time_test e he (hη.of_le (by norm_num)) _
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hp.contDiffAt) (hspatial x hx hΔ t ht')]
    ring

end OAI.Analysis.PDE.Concentration
