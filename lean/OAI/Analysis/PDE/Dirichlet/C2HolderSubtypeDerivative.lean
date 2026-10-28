import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- The derivative of a map restricted between linear subspaces is the
ambient derivative, after applying the two inclusion maps. -/
theorem derivative_commuting_inclusions
    {X Y E G : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (i : X →L[ℝ] E) (j : Y →L[ℝ] G)
    (F : X → Y) (H : E → G) (v : E) (u w : X)
    (hF : DifferentiableAt ℝ F u) (hH : DifferentiableAt ℝ H (v + i u))
    (heq : ∀ z, j (F z) = H (v + i z)) :
    j (fderiv ℝ F u w) = fderiv ℝ H (v + i u) (i w) := by
  have hleft : HasFDerivAt (fun z ↦ j (F z)) (j.comp (fderiv ℝ F u)) u :=
    j.hasFDerivAt.comp u hF.hasFDerivAt
  have hin : HasFDerivAt (fun z ↦ v + i z) i u := i.hasFDerivAt.const_add v
  have hright : HasFDerivAt (fun z ↦ j (F z))
      ((fderiv ℝ H (v + i u)).comp i) u := by
    simp_rw [heq]
    exact hH.hasFDerivAt.comp u hin
  exact congrArg (fun T : X →L[ℝ] G ↦ T w) (hleft.unique hright)

end OAI.Analysis.PDE.Dirichlet
