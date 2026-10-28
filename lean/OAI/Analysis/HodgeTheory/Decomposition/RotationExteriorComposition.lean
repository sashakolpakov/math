import OAI.Analysis.HodgeTheory.Decomposition.ComplexRotationDifferentials
import OAI.Analysis.HodgeTheory.Decomposition.ExteriorConstantBracket

/-! # Rotation Exterior Composition -/

namespace OAI.Analysis.HodgeTheory.Decomposition.RotationExteriorComposition.Constructions

noncomputable section

/-! Differentiating a local rotation identity, with all equalities taken
between the actual coefficient fields near the point. -/

open scoped _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

theorem rotationExterior_difference (b : Module.Basis ι ℝ E) (n : ℕ)
    (f g h : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (heq : (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation n (f y) - g y) =ᶠ[𝓝 x] (fun y => -h y)) :
    ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (extDeriv f x) - extDeriv g x =
      -CovectorSymbolAction.Constructions.twistedExteriorDerivative n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) f x - extDeriv h x := by
  have hCf : DifferentiableAt ℝ (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation n (f y)) x :=
    (ComplexRotationDifferentials.Constructions.complexFormRotation n).differentiableAt.comp x hf
  have hd := ExteriorConstantBracket.Constructions.directionalExteriorDerivative_congr n (ContinuousLinearMap.id ℝ E) heq
  rw [ExteriorConstantBracket.Constructions.directionalExteriorDerivative_sub n _ _ _ hCf hg,
    ExteriorConstantBracket.Constructions.directionalExteriorDerivative_neg, ExteriorConstantBracket.Constructions.directionalExteriorDerivative_id,
    ExteriorConstantBracket.Constructions.directionalExteriorDerivative_id, ExteriorConstantBracket.Constructions.directionalExteriorDerivative_id] at hd
  have hr := ComplexRotationDifferentials.Constructions.complexFormRotation_exterior b n f hf
  calc
    _ = (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (extDeriv f x) -
        extDeriv (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation n (f y)) x) +
      (extDeriv (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation n (f y)) x - extDeriv g x) := by abel
    _ = _ := by rw [hr, hd, sub_eq_add_neg]

end

end OAI.Analysis.HodgeTheory.Decomposition.RotationExteriorComposition.Constructions
