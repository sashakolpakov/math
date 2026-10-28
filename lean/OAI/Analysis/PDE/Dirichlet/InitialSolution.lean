import OAI.Analysis.PDE.Dirichlet.InitialDensity
import OAI.Analysis.PDE.Dirichlet.Path.Solution

open Set Module
open scoped ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- The actual initial solution of the continuity path is the defining
function itself. In particular the path's solution set is nonempty. -/
def SmoothPathSolution.initial {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (r B₀ F : CoordinateSpace n 4 → ℝ)
    (hr : ContDiff ℝ 4 r) (hB : ContDiff ℝ 4 B₀)
    (hrper : LatticePeriodic e lat r)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef) :
    SmoothPathSolution e lat r B₀ (initialDensity B₀ r) F where
  t := 0
  parameter := by constructor <;> norm_num
  u := r
  smooth := hr
  periodic := hrper
  zero := fun _ hx ↦ hx
  positive := by
    intro x hx
    have hadd := quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots
      (hB.of_le (by norm_num)) (hr.of_le (by norm_num)) (1 : ℝ) x
    simp only [one_smul] at hadd
    rw [hadd, OAI.LinearAlgebra.Moore.complexify_add]
    exact Matrix.PosDef.posSemidef_add (hbase x hx.le) (hpos x hx.le)
  equation := by
    intro x _
    simp [densityPath, initialDensity]

end OAI.Analysis.PDE.Dirichlet
