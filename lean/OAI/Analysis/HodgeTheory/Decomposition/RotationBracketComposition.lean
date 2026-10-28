import OAI.Analysis.HodgeTheory.Decomposition.LefschetzBracketRotation
import OAI.Analysis.HodgeTheory.Decomposition.ExteriorConstantBracket

/-! # Rotation Bracket Composition -/

namespace OAI.Analysis.HodgeTheory.Decomposition.RotationBracketComposition.Constructions

noncomputable section

/-! Composing a local rotation identity with the actual Kähler bracket. -/

open scoped _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

theorem rotationBracket_difference (b : Module.Basis ι ℝ E) (n : ℕ)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (f g h : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hKf : DifferentiableAt ℝ (fun y => K0 y (f y)) x)
    (hKCf : DifferentiableAt ℝ (fun y => K0 y (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (f y))) x)
    (hKg : DifferentiableAt ℝ (fun y => K0 y (g y)) x)
    (hK0 : ∀ y ∈ U, ∀ v, K0 y (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) v) = ComplexRotationDifferentials.Constructions.complexFormRotation n (K0 y v))
    (hK1 : ∀ v, K1 x (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1 + 1) v) = ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (K1 x v))
    (heq : (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (f y) - g y) =ᶠ[𝓝 x] (fun y => -h y)) :
    ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1)
        (ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K1 K0 f x) -
      ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K1 K0 g x =
      -ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n (ContinuousLinearMap.id ℝ E) K1 K0 f x -
        ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K1 K0 h x := by
  let J : E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℂ Complex.I
  have hCf : DifferentiableAt ℝ (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (f y)) x :=
    (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1)).differentiableAt.comp x hf
  have hd := ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_congr n J K1 K0 heq
  rw [ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_sub n J K1 K0 _ _ hCf hg hKCf hKg,
    ExteriorConstantBracket.Constructions.lefschetzTwistedBracket_neg] at hd
  have hr := LefschetzBracketRotation.Constructions.lefschetzTwistedBracket_rotation b n K0 K1 f hU hx hf hKf hK0 hK1
  calc
    _ = (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n J K1 K0 f x) -
        ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n J K1 K0 (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (f y)) x) +
      (ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n J K1 K0 (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (f y)) x -
        ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n J K1 K0 g x) := by abel
    _ = _ := by rw [hr, hd, sub_eq_add_neg]

end

end OAI.Analysis.HodgeTheory.Decomposition.RotationBracketComposition.Constructions
