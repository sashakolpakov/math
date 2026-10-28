import OAI.Analysis.PDE.Dirichlet.InitialSolution
import OAI.Analysis.PDE.Green.DensitySmooth

noncomputable section
open Set Module
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem contDiff_initialDensity_infty {n : ℕ}
    {B₀ r : CoordinateSpace n 4 → ℝ} (hB₀ : ContDiff ℝ ∞ B₀) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (initialDensity B₀ r) := by
  exact (OAI.LinearAlgebra.Moore.contDiff_mooreDet n ∞).comp
    (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_infty OAI.Analysis.Calculus.Quaternion.fourSlots (hB₀.add hr))

end OAI.Analysis.PDE.Dirichlet
