import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiCovectorMetricDual
import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiTwoFormCoefficients

/-! # Curvature Contraction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvatureContraction

noncomputable section

/-! The line-curvature contraction in the Bochner formula, expressed through the actual inverse metric. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

variable (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)

theorem complex_covector_sharp_sum (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (q L : E →L[ℝ] ℂ) :
    (∑ j, q (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap) * L (b j)) =
      L (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp q)) +
        Complex.I * L (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.imCLM.comp q)) := by
  have hr := congrArg L (Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions.bilinearMetricSharp_basis_expansion B hpos hB b (Complex.reCLM.comp q))
  have hi := congrArg L (Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions.bilinearMetricSharp_basis_expansion B hpos hB b (Complex.imCLM.comp q))
  simp only [map_sum, map_smul, Complex.real_smul, ContinuousLinearMap.comp_apply,
    Complex.reCLM_apply, Complex.imCLM_apply] at hr hi
  rw [← hr, ← hi, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ((q (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap)).re +
        (q (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap)).im * Complex.I) * L (b j) :=
      congrArg (fun z : ℂ => z * L (b j)) (Complex.re_add_im _).symm
    _ = _ := by ring

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def lineCurvatureContraction (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) : E →L[ℝ] ℂ :=
  ∑ j, AntiOneFormCoordinates.oneFormLinear a (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap) • AntiTwoFormCoefficients.twoFormBilinear F (b j)

def lineCurvatureAction (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  AntiOneFormCoordinates.oneFormLinearEquiv (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (lineCurvatureContraction b B F a))

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem lineCurvatureContraction_apply (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (w : E) :
    lineCurvatureContraction b B F a w =
      ∑ j, AntiOneFormCoordinates.oneFormLinear a (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap) * F ![b j, w] := by
  simp only [lineCurvatureContraction, sum_apply, smul_apply, smul_eq_mul, AntiTwoFormCoefficients.twoFormBilinear_apply]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem lineCurvatureContraction_sharp (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (w : E) :
    lineCurvatureContraction b B F a w =
      AntiTwoFormCoefficients.twoFormBilinear F (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear a))) w +
        Complex.I * AntiTwoFormCoefficients.twoFormBilinear F (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.imCLM.comp (AntiOneFormCoordinates.oneFormLinear a))) w := by
  rw [lineCurvatureContraction_apply]
  simpa only [ContinuousLinearMap.flip_apply, AntiTwoFormCoefficients.twoFormBilinear_apply] using
    complex_covector_sharp_sum b B hB hpos (AntiOneFormCoordinates.oneFormLinear a) ((AntiTwoFormCoefficients.twoFormBilinear F).flip w)

theorem lineCurvatureAction_apply (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (w : E) :
    lineCurvatureAction b B F a (fun _ => w) =
      (1 / 2 : ℂ) * ∑ j, (F ![b j, w] * AntiOneFormCoordinates.oneFormLinear a (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap) +
        Complex.I * (F ![b j, Complex.I • w] * AntiOneFormCoordinates.oneFormLinear a (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap))) := by
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (lineCurvatureContraction b B F a) w = _
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply]
  simp only [lineCurvatureContraction_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvatureContraction
