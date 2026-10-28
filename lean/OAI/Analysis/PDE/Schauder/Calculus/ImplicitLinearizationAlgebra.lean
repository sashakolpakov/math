import OAI.Analysis.PDE.Schauder.Calculus.LinearizationAlgebra

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {X Y Z W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Compose three established linearization identities without rebuilding
their concrete maps during elaboration. -/
theorem linearization_comp_eq_of_eq
    {F₁ F₂ : Z →L[ℝ] W} {M : Y →L[ℝ] Z} {P : X →L[ℝ] Y}
    {L : X →L[ℝ] Z} {G : Y →L[ℝ] W}
    (hF : F₁ = F₂) (hL : M.comp P = L) (hG : G = F₂.comp M) :
    F₁.comp L = G.comp P := by
  rw [hF, ← hL, hG, ContinuousLinearMap.comp_assoc]

end OAI.Analysis.PDE.Schauder
