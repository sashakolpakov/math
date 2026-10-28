import OAI.Analysis.HodgeTheory.Decomposition.ExteriorRotation

/-! # Complex Rotation Differentials -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ComplexRotationDifferentials.Constructions

noncomputable section

/-! Infinitesimal complex rotation interchanges the ordinary and twisted
exterior derivatives through their exact commutators. -/

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

omit [Fintype ι] [FiniteDimensional ℝ E] in
def complexFormRotation (n : ℕ) : DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n :=
  CovectorConnection.Constructions.covectorInfinitesimalAction n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem complexTangentRotation_squared :
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I : E →L[ℝ] E).comp
      (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) = -ContinuousLinearMap.id ℝ E := by
  ext v
  change Complex.I • (Complex.I • v) = -v
  rw [smul_smul, Complex.I_mul_I]
  exact neg_one_smul ℂ v

omit [Fintype ι] [FiniteDimensional ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem directionalExteriorDerivative_neg_direction (n : ℕ) (A : E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    ExteriorConstantBracket.Constructions.directionalExteriorDerivative n (-A) a x = -ExteriorConstantBracket.Constructions.directionalExteriorDerivative n A a x := by
  simp only [ExteriorConstantBracket.Constructions.directionalExteriorDerivative, ExteriorConstantBracket.Constructions.alternationWithDirection_apply, ContinuousLinearMap.comp_neg]
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ).map_neg ((fderiv ℝ a x).comp A)

theorem complexFormRotation_exterior (b : Module.Basis ι ℝ E) (n : ℕ)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : DifferentiableAt ℝ a x) :
    complexFormRotation (n + 1) (extDeriv a x) -
      extDeriv (fun y => complexFormRotation n (a y)) x =
      -CovectorSymbolAction.Constructions.twistedExteriorDerivative n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a x := by
  have h := ExteriorRotation.Constructions.covectorInfinitesimalAction_directionalExterior b n
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) (ContinuousLinearMap.id ℝ E) a ha
  simpa only [ExteriorConstantBracket.Constructions.directionalExteriorDerivative_id, ContinuousLinearMap.id_comp,
    ExteriorConstantBracket.Constructions.directionalExteriorDerivative_twisted, neg_neg, complexFormRotation] using h

theorem complexFormRotation_twisted (b : Module.Basis ι ℝ E) (n : ℕ)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : DifferentiableAt ℝ a x) :
    complexFormRotation (n + 1)
        (CovectorSymbolAction.Constructions.twistedExteriorDerivative n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a x) -
      CovectorSymbolAction.Constructions.twistedExteriorDerivative n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
        (fun y => complexFormRotation n (a y)) x = extDeriv a x := by
  have h := ExteriorRotation.Constructions.covectorInfinitesimalAction_directionalExterior b n
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a ha
  rw [complexTangentRotation_squared, directionalExteriorDerivative_neg_direction,
    ExteriorConstantBracket.Constructions.directionalExteriorDerivative_id] at h
  simp only [ExteriorConstantBracket.Constructions.directionalExteriorDerivative_twisted, map_neg, sub_neg_eq_add]
  have hn := congrArg (fun f : DifferentialForms.Manifold.Basic.FormValue E (n + 1) => -f) h
  rw [neg_neg] at hn
  convert! hn using 1
  abel

end

end OAI.Analysis.HodgeTheory.Decomposition.ComplexRotationDifferentials.Constructions
