import OAI.Analysis.HodgeTheory.Decomposition.ComplexMetric

/-! # Derivative Complex Linearity -/

namespace OAI.Analysis.HodgeTheory.Decomposition.DerivativeComplexLinearity.Constructions

noncomputable section

/-! Derivatives of the actual complex-linear metric operators remain
complex-linear in the form coefficient argument. -/

theorem fderiv_operator_complex_smul {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : E → F →L[ℝ] G) {x : E} (hA : DifferentiableAt ℝ A x)
    (hℂ : ∀ (y : E) (c : ℂ) (u : F), A y (c • u) = c • A y u)
    (v : E) (c : ℂ) (u : F) :
    fderiv ℝ A x v (c • u) = c • fderiv ℝ A x v u := by
  let P := ContinuousLinearMap.apply ℝ G (c • u)
  let Q := ContinuousLinearMap.apply ℝ G u
  let C := (c • ContinuousLinearMap.id ℂ G).restrictScalars ℝ
  have hleft := P.hasFDerivAt.comp x hA.hasFDerivAt
  have hright := C.hasFDerivAt.comp x (Q.hasFDerivAt.comp x hA.hasFDerivAt)
  have heq : (fun y => C (Q (A y))) = (fun y => P (A y)) := by
    funext y
    exact (hℂ y c u).symm
  have hright' : HasFDerivAt (fun y => P (A y)) (C.comp (Q.comp (fderiv ℝ A x))) x := by
    exact heq ▸ hright
  exact congrArg (fun B : E →L[ℝ] G => B v) (hleft.unique hright')

theorem projectiveWeightedFormOperator_derivative_complex_smul
    (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
    (x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hx : x ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (c : ℂ)
    (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    fderiv ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n) x v (c • u) =
      c • fderiv ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n) x v u := by
  apply fderiv_operator_complex_smul (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n)
    (((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n).contDiffAt
      ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hx)).differentiableAt (by simp))
  exact ComplexMetric.Constructions.projectiveWeightedFormOperator_complex_smul V e n

end

end OAI.Analysis.HodgeTheory.Decomposition.DerivativeComplexLinearity.Constructions
