import OAI.Analysis.PDE.Concentration.Physical.Matrix
import OAI.Analysis.PDE.Concentration.NullHessian
import OAI.Analysis.PDE.Concentration.Physical.Coordinates

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix ContDiff

def physicalBackground (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) : ℝ :=
  ‖OAI.Analysis.Calculus.Current.phi (physicalToNullCurrentPoint d x).2‖ ^ 2

theorem physicalBackground_hessian (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (physicalBackground d) x =
      physicalMatrix (OAI.Analysis.Calculus.Current.backgroundHessian (physicalToNullCurrentPoint d x).2) := by
  have hU : IsOpen {z : OAI.Analysis.Calculus.Current.Index d → ℂ | z none ≠ 0} :=
    isOpen_ne.preimage (continuous_apply none)
  have hf : ContDiffOn ℝ 2 (fun z : OAI.Analysis.Calculus.Current.Index d → ℂ => ‖OAI.Analysis.Calculus.Current.phi z‖ ^ 2) {z | z none ≠ 0} := by
    intro z hz
    exact (((OAI.Analysis.Calculus.Current.contDiffAt_phi_real z hz).norm_sq ℂ).of_le (by norm_num)).contDiffWithinAt
  exact quaternionHessian_physical_null hU hf x hx

theorem physicalBackground_mul_current_zero {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (hh : 0 < h) (ha : a ≠ 0) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (physicalBackground d) x *
      physicalPacketCurrent h a κ cR cI v x = 0 := by
  rw [physicalBackground_hessian d x hx, physicalPacketCurrent_eq_physicalMatrix]
  apply physicalMatrix_mul_zero
  exact OAI.Analysis.Calculus.Current.regularizedCurrent_background_mul _ _ h a κ cR cI v
    (physicalToNullCurrentPoint d x).1 (physicalToNullCurrentPoint d x).2 ha hx
    (OAI.Analysis.Calculus.Current.integrable_sourceWave_translates h hh κ cR cI v _ _ hx)

theorem physicalCurrent_background_pairing_zero {d : ℕ} {ι : Type*} [Fintype ι]
    (h a : ℝ) (hh : 0 < h) (ha : a ≠ 0) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3) (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    OAI.LinearAlgebra.Moore.realTrace (physicalPacketCurrent h a κ cR cI v x *
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (physicalBackground d) x) = 0 := by
  rw [OAI.LinearAlgebra.Moore.realTrace_mul_comm, physicalBackground_mul_current_zero h a hh ha κ cR cI v x hx]
  simp [OAI.LinearAlgebra.Moore.realTrace]

end OAI.Analysis.PDE.Concentration
