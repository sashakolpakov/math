import OAI.Analysis.PDE.Concentration.Physical.Background
import OAI.LinearAlgebra.Moore.OuterPencil

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix

def physicalVector {d : ℕ} (v : OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) : Fin (d + 2) → Quaternion ℝ :=
  (OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d))ᴴ *ᵥ (v ∘ nullIndexEquiv d)

theorem physicalMatrix_smul {d : ℕ} (c : ℝ) (M : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)) :
    physicalMatrix (c • M) = c • physicalMatrix M := by
  simp [physicalMatrix, Matrix.submatrix_smul]

theorem physicalMatrix_outer {d : ℕ} (v : OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) :
    physicalMatrix (OAI.Analysis.Calculus.Quaternion.outer v) = OAI.Analysis.Calculus.Quaternion.outer (physicalVector v) := by
  change (OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d))ᴴ * OAI.Analysis.Calculus.Quaternion.outer (v ∘ nullIndexEquiv d) *
    OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d) = _
  simpa only [Matrix.conjTranspose_conjTranspose, physicalVector] using!
    OAI.LinearAlgebra.Moore.outer_congruence (OAI.Analysis.PDE.Dirichlet.realLift (nullRotation d))ᴴ (v ∘ nullIndexEquiv d)

theorem physicalBackground_hessian_rank_one (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (physicalBackground d) x = (4 : ℝ) •
      OAI.Analysis.Calculus.Quaternion.outer (physicalVector (fun b =>
        OAI.Analysis.Calculus.Current.complexK (star (OAI.Analysis.Calculus.Current.phaseRow (OAI.Analysis.Calculus.Current.ratio (physicalToNullCurrentPoint d x).2) b)))) := by
  rw [physicalBackground_hessian d x hx, OAI.Analysis.Calculus.Current.backgroundHessian_formula _ hx,
    physicalMatrix_smul, physicalMatrix_outer]

theorem physicalBackground_mooreDet_zero (d : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hx : (physicalToNullCurrentPoint d x).2 none ≠ 0) :
    OAI.LinearAlgebra.Moore.mooreDet (d + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.threeSlots (physicalBackground d) x) = 0 := by
  rw [physicalBackground_hessian_rank_one d x hx, OAI.LinearAlgebra.Moore.mooreDet_smul, OAI.LinearAlgebra.Moore.mooreDet_outer_zero]
  simp

end OAI.Analysis.PDE.Concentration
