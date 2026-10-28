import OAI.Analysis.Normed.Function.Holder.Boundary.LogCoefficient

noncomputable section
open Set
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

local instance actualLogEndGroup (n : ℕ) :
    NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) := inferInstance
local instance actualLogEndSpace (n : ℕ) :
    NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) := inferInstance

/-- The actual logarithmic linearization, uniformly bounded using only
the original C²,α norm and the positive density lower bound. -/
theorem exists_actual_log_coefficient_bound {n : ℕ}
    {Ω K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α R μ : ℝ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hμ : 0 < μ) :
    ∃ N ≥ 0, ∀ (u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α),
      ‖U‖ ≤ R →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ x ∈ K, μ ≤ OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)) →
      ∃ A : OAI.Analysis.Normed.Function.Holder.HolderMap K (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) α,
        ‖A‖ ≤ N ∧ ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) := by
  obtain ⟨N,hN,hfield⟩ := OAI.Analysis.PDE.Dirichlet.exists_logRealCoefficient_bound (hΩK := hΩK) hα hR hμ
  refine ⟨N,hN,?_⟩
  intro u U hUn hU₂ hdet
  have hH (x : K) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots U) x =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x := by
    change OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (fun i j => OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x
      (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)) = _
    rw [hU₂]
    rfl
  obtain ⟨A,hA,hAn⟩ := hfield U hUn (fun x => by rw [hH]; exact hdet x x.property)
  exact ⟨A,hAn,fun x => (hA x).trans (congrArg OAI.Analysis.PDE.Dirichlet.logRealOperator (hH x))⟩

end OAI.Analysis.PDE.Elliptic
