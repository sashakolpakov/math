import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Reflection

/-! Compact support is preserved by flat odd reflection. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem hasCompactSupport_oddNormalExtension (e : E) (u : E → ℝ)
    (hu : HasCompactSupport u) : HasCompactSupport (oddNormalExtension e u) := by
  have hr : HasCompactSupport (u ∘ normalReflection e) := hu.comp_homeomorph (normalReflection e).toHomeomorph
  apply HasCompactSupport.intro' (hu.union hr) ((isClosed_tsupport u).union (isClosed_tsupport (u ∘ normalReflection e)))
  intro x hx
  have hx₁ : x ∉ tsupport u := fun h => hx (Or.inl h)
  have hx₂ : x ∉ tsupport (u ∘ normalReflection e) := fun h => hx (Or.inr h)
  have hu₁ := image_eq_zero_of_notMem_tsupport hx₁
  have hu₂ := image_eq_zero_of_notMem_tsupport hx₂
  simp only [Function.comp_apply] at hu₂
  simp [oddNormalExtension, hu₁, hu₂]

end OAI.Analysis.PDE.Schauder
