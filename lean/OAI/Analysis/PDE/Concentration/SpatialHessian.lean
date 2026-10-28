import OAI.Analysis.PDE.Concentration.Physical.Determinant
import OAI.Analysis.PDE.Concentration.CovarianceLocal
import OAI.Analysis.PDE.Green.Physical.CellGeometry

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped ContDiff Matrix ComplexOrder

theorem physicalSpatialProjection_coordinateVector (d : ℕ) (i : Fin (d + 1)) (α : Fin 3) :
    OAI.Analysis.PDE.Green.physicalSpatialProjection d (OAI.Analysis.PDE.Dirichlet.coordinateVector (i, α)) = OAI.Analysis.Calculus.Quaternion.imaginaryDirection (finSuccEquiv d i) α := by
  ext j
  have hj : (finSuccEquiv d).symm j = i ↔ j = finSuccEquiv d i := by
    rw [Equiv.symm_apply_eq]
  have hi : i = (finSuccEquiv d).symm j ↔ j = finSuccEquiv d i := by
    rw [eq_comm, Equiv.symm_apply_eq]
  fin_cases α <;>
    simp [OAI.Analysis.PDE.Green.physicalSpatialProjection_apply, OAI.Analysis.PDE.Dirichlet.coordinateVector, PiLp.single_apply,
      OAI.Analysis.Calculus.Quaternion.imaginaryDirection, OAI.Analysis.Calculus.Quaternion.imaginarySlot, Pi.single_apply, hj]
  all_goals split_ifs <;> simp

theorem quaternionHessian_spatialProjection {d : ℕ} {f : (Option (Fin d) → ℂ) → ℝ}
    {U : Set (Option (Fin d) → ℂ)} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (hx : OAI.Analysis.PDE.Green.physicalSpatialProjection d x ∈ U) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (f ∘ OAI.Analysis.PDE.Green.physicalSpatialProjection d) x =
      (OAI.Analysis.Calculus.Quaternion.imaginaryHessian f (OAI.Analysis.PDE.Green.physicalSpatialProjection d x)).submatrix (finSuccEquiv d) (finSuccEquiv d) := by
  apply Matrix.ext
  intro a b
  simp only [OAI.Analysis.PDE.Dirichlet.quaternionHessian, OAI.Analysis.PDE.Dirichlet.realHessian, OAI.Analysis.Calculus.Quaternion.hessianMap, OAI.Analysis.Calculus.Quaternion.imaginaryHessian, Matrix.submatrix_apply]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [second_fderiv_comp_linear_on (OAI.Analysis.PDE.Green.physicalSpatialProjection d) hU hf hx,
    physicalSpatialProjection_coordinateVector, physicalSpatialProjection_coordinateVector]

def spatialDefiningFunction (d : ℕ) (a : ℝ) (τ : ℂ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ :=
  OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ ∘ OAI.Analysis.PDE.Green.physicalSpatialProjection d

def spatialBackgroundFunction (d : ℕ) (τ : ℂ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ :=
  (fun q => ‖OAI.Analysis.Calculus.Current.phi (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)‖ ^ 2) ∘ OAI.Analysis.PDE.Green.physicalSpatialProjection d

theorem quaternionHessian_spatialDefiningFunction (d : ℕ) (a : ℝ) (τ : ℂ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (hx : OAI.Analysis.PDE.Green.physicalSpatialProjection d x ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain τ) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (spatialDefiningFunction d a τ) x =
      spatialDefiningMatrix d a τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) :=
  quaternionHessian_spatialProjection (OAI.Analysis.Calculus.Current.isOpen_physicalRegularDomain τ)
    ((OAI.Analysis.Calculus.Current.contDiffOn_physicalFiberDefining (1 / 10) a τ).of_le (by norm_num)) x hx

theorem quaternionHessian_spatialBackgroundFunction (d : ℕ) (τ : ℂ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (hx : OAI.Analysis.Calculus.Current.physicalEmbedding τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) none ≠ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (spatialBackgroundFunction d τ) x =
      spatialBackgroundMatrix d τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) := by
  let U := {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage
    ((continuous_apply none).comp (OAI.Analysis.Calculus.Current.contDiff_physicalEmbedding τ).continuous)
  have hf : ContDiffOn ℝ 2 (fun q : Option (Fin d) → ℂ => ‖OAI.Analysis.Calculus.Current.phi (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)‖ ^ 2) U := by
    intro q hq
    exact ((((OAI.Analysis.Calculus.Current.contDiffAt_phi_real _ hq).comp q (OAI.Analysis.Calculus.Current.contDiff_physicalEmbedding τ).contDiffAt).norm_sq ℂ).of_le
      (by norm_num)).contDiffWithinAt
  exact quaternionHessian_spatialProjection hU hf x hx

end OAI.Analysis.PDE.Concentration
