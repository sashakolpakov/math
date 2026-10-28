import OAI.Analysis.PDE.Concentration.Lattice.Quaternion
import OAI.Analysis.PDE.Concentration.Lattice.Periodicity
import OAI.Analysis.PDE.Green.CellPencil

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix _root_.MeasureTheory OAI.Analysis.PDE.Green OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder

theorem pencil_second_green_lattice {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r u B v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B) (hv : ContDiff ℝ 2 v) (t : ℝ)
    (hrne : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin n → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0)
    (hface : CompatibleLatticeFaces c L a b r (OAI.Analysis.PDE.Green.secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u v)) :
    (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0}, u x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0}, v x *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  apply moore_cofactor_second_green_lattice e c L a b hab
    (hB.add (contDiff_const.mul hu)) (hu.of_le (by norm_num)) hv hr hrne huz
    (OAI.Analysis.PDE.Green.boundary_pencil_normal_cofactor_zero e hr (hu.of_le (by norm_num))
      (hB.of_le (by norm_num)) t huz hcommon) hface

theorem determinant_pencil_energy_variation_lattice {n s m : ℕ}
    (e : Fin s → Quaternion ℝ) (c : (Fin n × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r u B v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hr : ContDiff ℝ 2 r)
    (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B) (hv : ContDiff ℝ 3 v)
    (hrne : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin n → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0)
    (hdata : CompatibleLatticePencilData c L a b r B u v) :
    (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
      ∫ t in (0 : ℝ)..1, u x * OAI.LinearAlgebra.Moore.mooreDifferential n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e v x)) =
    ∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0}, v x *
      (OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
        OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
  have hb := (isBounded_euclideanLatticeCell c L a b).subset
    (inter_subset_left : (euclideanLatticeCell c L a b ∩ {x | r x < 0}) ⊆ _)
  have hgreen (t : ℝ) := pencil_second_green_lattice e c L a b hab hr hu hB
    (hv.of_le (by norm_num)) t hrne huz hcommon
    (pencil_compatible_lattice_faces e c L a b r B u v hdata t)
  simp_rw [OAI.Analysis.PDE.Green.quaternionHessian_add_mul e (hB.of_le (by norm_num))
    (hu.of_le (by norm_num))] at hgreen ⊢
  have he := OAI.Analysis.PDE.Green.integrate_pencil_green hb hu.continuous hv.continuous
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hB)
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hu)
    (OAI.Analysis.PDE.Energy.continuous_quaternionHessian_three e hv) hgreen
  simpa only [OAI.Analysis.PDE.Energy.hessian_sum e (hB.of_le (by norm_num))
    (hu.of_le (by norm_num))] using he

/-- The actual determinant energy obeys the weak time-Laplacian identity
on a lattice cell, with periodicity imposed only on primitive data. -/
theorem determinant_energy_weak_time_laplacian_lattice {n s m : ℕ}
    (e : Fin s → Quaternion ℝ)
    (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (c : (Fin (n + 1) × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r u B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 3 u) (hB : ContDiff ℝ 3 B)
    (hη : ContDiff ℝ 3 η)
    (hrne : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ y, r y = 0 → u y = 0)
    (hcommon : ∀ x, r x = 0 → ∃ w : Fin (n + 1) → Quaternion ℝ, w ≠ 0 ∧
      OAI.Analysis.PDE.Dirichlet.quaternionHessian e r x *ᵥ w = 0 ∧ OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x *ᵥ w = 0 ∧
      star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ⬝ᵥ w = 0)
    (hspatial : ∀ x ∈ euclideanLatticeCell c L a b ∩ {x | r x < 0},
      ∀ t ∈ Icc (0 : ℝ) 1,
      (OAI.LinearAlgebra.Moore.complexify ((OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x).submatrix
        Fin.succ Fin.succ)).PosSemidef)
    (hdata : CompatibleLatticePencilData c L a b r B u (fun x => η (OAI.Analysis.PDE.Green.timeProjection n s x))) :
    (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
      Laplacian.laplacian η (OAI.Analysis.PDE.Green.timeProjection n s x) * OAI.Analysis.PDE.Green.spatialPencilEnergyDensity e B u x) =
    ∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
      η (OAI.Analysis.PDE.Green.timeProjection n s x) *
      (OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
        OAI.LinearAlgebra.Moore.mooreDet (n + 1) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) := by
  have htest : ContDiff ℝ 3 (fun y => η (OAI.Analysis.PDE.Green.timeProjection n s y)) :=
    hη.comp (OAI.Analysis.PDE.Green.timeProjection n s).contDiff
  have hv := determinant_pencil_energy_variation_lattice e c L a b hab hr hu hB htest
    hrne huz hcommon hdata
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
  rw [OAI.Analysis.PDE.Green.mooreDifferential_time_test e he (hη.of_le (by norm_num)) _
    (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hp.contDiffAt) (hspatial x hx t ht')]
  ring

end OAI.Analysis.PDE.Concentration
