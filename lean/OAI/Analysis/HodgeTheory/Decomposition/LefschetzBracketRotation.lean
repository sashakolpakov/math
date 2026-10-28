import OAI.Analysis.HodgeTheory.Decomposition.ExteriorConstantBracket
import OAI.Analysis.HodgeTheory.Decomposition.ComplexRotationDifferentials

/-! # Lefschetz Bracket Rotation -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LefschetzBracketRotation.Constructions

noncomputable section

/-! The rotation commutator of the Kähler derived bracket is the opposite
derived bracket for the untwisted direction, including degree one. -/

open scoped _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

theorem lefschetzTwistedBracket_rotation_zero (b : Module.Basis ι ℝ E)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E 2 →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E 0) (a : E → DifferentialForms.Manifold.Basic.FormValue E 1) {x : E}
    (ha : DifferentiableAt ℝ a x)
    (hK : ∀ v, K0 x (ComplexRotationDifferentials.Constructions.complexFormRotation 2 v) = ComplexRotationDifferentials.Constructions.complexFormRotation 0 (K0 x v)) :
    ComplexRotationDifferentials.Constructions.complexFormRotation 0 (ExteriorConstantBracket.Constructions.lefschetzTwistedBracketZero (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K0 a x) -
      ExteriorConstantBracket.Constructions.lefschetzTwistedBracketZero (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K0
        (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation 1 (a y)) x =
      -ExteriorConstantBracket.Constructions.lefschetzTwistedBracketZero (ContinuousLinearMap.id ℝ E) K0 a x := by
  have h := congrArg (K0 x) (ComplexRotationDifferentials.Constructions.complexFormRotation_twisted b 1 a ha)
  rw [map_sub, hK] at h
  change _ = -K0 x (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 (ContinuousLinearMap.id ℝ E) a x)
  rw [ExteriorConstantBracket.Constructions.directionalExteriorDerivative_twisted, ExteriorConstantBracket.Constructions.directionalExteriorDerivative_id, map_neg, neg_neg]
  exact h

theorem lefschetzTwistedBracket_rotation (b : Module.Basis ι ℝ E) (n : ℕ)
    (K0 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n)
    (K1 : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E (n + 1))
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) (ha : DifferentiableAt ℝ a x)
    (hKa : DifferentiableAt ℝ (fun y => K0 y (a y)) x)
    (hK0 : ∀ y ∈ U, ∀ v, K0 y (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) v) = ComplexRotationDifferentials.Constructions.complexFormRotation n (K0 y v))
    (hK1 : ∀ v, K1 x (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1 + 1) v) = ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (K1 x v)) :
    ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1)
        (ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K1 K0 a x) -
      ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) K1 K0
        (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (a y)) x =
      -ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n (ContinuousLinearMap.id ℝ E) K1 K0 a x := by
  let J : E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℂ Complex.I
  let g : E → DifferentialForms.Manifold.Basic.FormValue E n := fun y => K0 y (a y)
  have heq : (fun y => K0 y (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (a y))) =ᶠ[𝓝 x]
      (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation n (g y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hK0 y hy (a y)
  have h1 := congrArg (K1 x) (ComplexRotationDifferentials.Constructions.complexFormRotation_twisted b (n + 1 + 1) a ha)
  rw [map_sub] at h1
  have h0 := ComplexRotationDifferentials.Constructions.complexFormRotation_twisted b n g hKa
  have hcalc : ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n J K1 K0 a x) -
      ExteriorConstantBracket.Constructions.lefschetzTwistedBracket n J K1 K0 (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (a y)) x =
      K1 x (extDeriv a x) - extDeriv g x := by
    rw [ExteriorConstantBracket.Constructions.lefschetzTwistedBracket, ExteriorConstantBracket.Constructions.lefschetzTwistedBracket, map_sub, ← hK1,
      ExteriorConstantBracket.Constructions.twistedExteriorDerivative_congr n J heq]
    calc
      _ = (K1 x (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1 + 1) (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) J a x)) -
          K1 x (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) J (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1 + 1) (a y)) x)) -
        (ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (CovectorSymbolAction.Constructions.twistedExteriorDerivative n J g x) -
          CovectorSymbolAction.Constructions.twistedExteriorDerivative n J (fun y => ComplexRotationDifferentials.Constructions.complexFormRotation n (g y)) x) := by
            change _ - ComplexRotationDifferentials.Constructions.complexFormRotation (n + 1) (CovectorSymbolAction.Constructions.twistedExteriorDerivative n J g x) - (_ - _) = _
            abel
      _ = _ := by rw [h1, h0]
  rw [hcalc]
  simp only [ExteriorConstantBracket.Constructions.lefschetzTwistedBracket, ExteriorConstantBracket.Constructions.directionalExteriorDerivative_twisted,
    ExteriorConstantBracket.Constructions.directionalExteriorDerivative_id, map_neg]
  change K1 x (extDeriv a x) - extDeriv g x = -(-K1 x (extDeriv a x) - -extDeriv g x)
  abel

end

end OAI.Analysis.HodgeTheory.Decomposition.LefschetzBracketRotation.Constructions
