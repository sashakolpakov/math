import OAI.Analysis.PDE.Green.CellQuaternion
import OAI.Analysis.PDE.Green.WeakLaplacian

/-! Determinant energy and its weak time Laplacian on periodic cells. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem determinant_pencil_energy_variation_cell {n s m : ℕ}
    (e : Fin s → Quaternion ℝ) (c : (Fin n × Fin s) ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r u B v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B) (hv : ContDiff ℝ 3 v)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin n → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0)
    (hface : ∀ t : ℝ, CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u v)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∫ t in (0 : ℝ)..1, u x * OAI.LinearAlgebra.Moore.mooreDifferential n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, v x *
      (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
        OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
  have hb := (isBounded_euclidean_cell c a b).subset
    (inter_subset_left : ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) ⊆ _)
  have hgreen (t : ℝ) := pencil_second_green_cell e c a b hab hr hu hB
    (hv.of_le (by norm_num)) t hrne huz hcommon (hface t)
  simp_rw [quaternionHessian_add_mul e (hB.of_le (by norm_num))
    (hu.of_le (by norm_num))] at hgreen ⊢
  have he := integrate_pencil_green hb hu.continuous hv.continuous
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hB)
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hu)
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hv) hgreen
  simpa only [OAI.Analysis.PDE.Energy.hessian_sum e (hB.of_le (by norm_num))
    (hu.of_le (by norm_num))] using he

/-- The determinant energy identity on a cell. Periodic faces cancel, and the
lateral cancellation is derived from the shared fiber kernel and zero data. -/
theorem determinant_energy_weak_time_laplacian_cell {n s m : ℕ}
    (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (c : (Fin (n + 1) × Fin s) ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B)
    (hη : ContDiff ℝ 3 η)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin (n + 1) → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0)
    (hspatial : ∀ x ∈ (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∀ t ∈ Icc (0 : ℝ) 1,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x).submatrix
        Fin.succ Fin.succ)).PosSemidef)
    (hface : ∀ t : ℝ, CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor (n + 1)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u
      (fun x => η (timeProjection n s x)))) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      Laplacian.laplacian η (timeProjection n s x) * spatialPencilEnergyDensity e B u x) =
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      η (timeProjection n s x) *
      (OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
  have htest : ContDiff ℝ 3 (fun y => η (timeProjection n s y)) :=
    hη.comp (timeProjection n s).contDiff
  have hv := determinant_pencil_energy_variation_cell e c a b hab hr hu hB htest
    hrne huz hcommon hface
  rw [← hv]
  apply setIntegral_congr_fun ((isClosed_Icc.preimage
    (euclideanCoordinates c).continuous).measurableSet.inter
    (isOpen_lt hr.continuous continuous_const).measurableSet)
  intro x hx
  dsimp only
  unfold spatialPencilEnergyDensity
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
  have hp : ContDiff ℝ 2 (fun y => B y + t * u y) :=
    (hB.of_le (by norm_num)).add (contDiff_const.mul (hu.of_le (by norm_num)))
  dsimp only
  rw [mooreDifferential_time_test e he (hη.of_le (by norm_num)) _
    (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hp.contDiffAt) (hspatial x hx t ht')]
  ring

end OAI.Analysis.PDE.Green
