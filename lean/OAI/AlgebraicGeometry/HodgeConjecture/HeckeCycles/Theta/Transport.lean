import OAI.RepresentationTheory.Hecke.RadialDilation.Prerequisites
import OAI.RepresentationTheory.Theta.Adelic.Prerequisites

/-! # Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Transport.CM

/-! Transport the complete CompletedTheta proposition between its two matrix-norm
interfaces. The three algebraic conclusions are unchanged; smoothness is
transported by the continuous linear identity on matrix coordinates. The
uncompleted Poisson law remains a hypothesis on both sides. -/

universe u

section Norms
variable {I : Type u} [Fintype I]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

open scoped _root_.Matrix.Norms.Elementwise in
def smoothElementwise (f : Matrix I I ℂ → F) (s : Set (Matrix I I ℂ)) : Prop :=
  ContDiffOn ℝ ⊤ f s

open scoped _root_.Matrix.Norms.Operator in
def smoothOperator (f : Matrix I I ℂ → F) (s : Set (Matrix I I ℂ)) : Prop :=
  ContDiffOn ℝ ⊤ f s

theorem smooth_norm_iff (f : Matrix I I ℂ → F) (s : Set (Matrix I I ℂ)) :
    smoothElementwise f s ↔ smoothOperator f s := by
  constructor
  · intro h
    exact @ContDiffOn.comp_continuousLinearMap ℝ (Matrix I I ℂ) F (Matrix I I ℂ) _
      Matrix.normedAddCommGroup Matrix.normedSpace _ _
      Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
      s f ⊤ h (ContinuousLinearMap.id ℝ (Matrix I I ℂ))
  · intro h
    exact @ContDiffOn.comp_continuousLinearMap ℝ (Matrix I I ℂ) F (Matrix I I ℂ) _
      Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace _ _
      Matrix.normedAddCommGroup Matrix.normedSpace
      s f ⊤ h (ContinuousLinearMap.id ℝ (Matrix I I ℂ))
end Norms

theorem full_input_iff :
    RepresentationTheory.Theta.Adelic.Prerequisites.ThetaInput.{u} ↔
      ∀ (I : Type u) [Fintype I] [DecidableEq I], @RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.Proposition I _ _ := by
  constructor
  · intro h I _ _ L Lnew _ _ φ φnew gQ g hA hB hC hD halfDet hHalf hPoisson
    obtain ⟨hs, hrest⟩ := h L Lnew φ φnew gQ g hA hB hC hD halfDet hHalf hPoisson
    refine ⟨?_, hrest⟩
    intro a
    exact (smooth_norm_iff (RepresentationTheory.Theta.Definitions.completedTensor L φ a) _).mp (hs a)
  · intro h I _ _ L Lnew _ _ φ φnew gQ g hA hB hC hD halfDet hHalf hPoisson
    obtain ⟨hs, hrest⟩ := h I L Lnew φ φnew gQ g hA hB hC hD halfDet hHalf hPoisson
    refine ⟨?_, hrest⟩
    intro a
    exact (smooth_norm_iff (RepresentationTheory.Hecke.RadialDilation.Prerequisites.Core.Theta.completedTensor L φ a) _).mpr (hs a)

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Transport.CM
