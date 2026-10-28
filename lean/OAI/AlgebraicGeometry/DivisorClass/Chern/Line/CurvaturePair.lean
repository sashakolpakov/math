import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvatureContraction

/-! # Curvature Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvaturePair

noncomputable section

/-! The line-curvature term pairs with an antiholomorphic covector with the exact positive sign of i times curvature. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [Fintype ι] [LinearOrder ι] [FiniteDimensional ℝ E] in
theorem twoFormBilinear_self (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (v : E) : AntiTwoFormCoefficients.twoFormBilinear F v v = 0 := by
  rw [AntiTwoFormCoefficients.twoFormBilinear_apply]
  exact F.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)

omit [Fintype ι] [LinearOrder ι] [FiniteDimensional ℝ E] in
theorem twoFormBilinear_swap (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (v w : E) :
    AntiTwoFormCoefficients.twoFormBilinear F v w = -AntiTwoFormCoefficients.twoFormBilinear F w v := by
  rw [AntiTwoFormCoefficients.twoFormBilinear_apply, AntiTwoFormCoefficients.twoFormBilinear_apply]
  have ht : ![w, v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v, w] := by
    funext j
    fin_cases j <;> rfl
  have h := F.toAlternatingMap.map_swap ![w, v] (i := 0) (j := 1) (by decide)
  rw [ht] at h
  exact h

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
variable (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
  (hB : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v)
  (hBJ : ∀ v w, B (Complex.I • v) w = -B v (Complex.I • w))

omit hB hpos hBJ [LinearOrder ι] in
theorem lineCurvatureAction_anti (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 (CurvatureContraction.lineCurvatureAction b B F a) := by
  intro c t
  rw [AntiOneFormCoordinates.oneFormLinear_reconstruct, AntiOneFormCoordinates.oneFormLinear_reconstruct]
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (CurvatureContraction.lineCurvatureContraction b B F a) ((c : ℂ) • t 0) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 1 c * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (CurvatureContraction.lineCurvatureContraction b B F a) (t 0)
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, pow_one, one_mul, smul_eq_mul]

include hB hpos hBJ

theorem antiOneCovector_metric_pair (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 a) (hc : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 c) :
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a c).re =
      2 * (AntiOneFormCoordinates.oneFormLinear a (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear c)))).re := by
  rw [OneCovectorMetricSharp.bilinearFormMetricPair_one_re_sharp b B hB hpos,
    AntiCovectorMetricDual.antiOneCovector_im_sharp B hpos hBJ c hc, map_neg, Complex.neg_im,
    AntiCovectorMetricDual.antiOneCovector_im_J a ha, neg_neg]
  ring

omit [LinearOrder ι] in
theorem lineCurvatureAction_real_dual (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 a) :
    let r := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear a))
    AntiOneFormCoordinates.oneFormLinear (CurvatureContraction.lineCurvatureAction b B F a) r = Complex.I * AntiTwoFormCoefficients.twoFormBilinear F r (Complex.I • r) := by
  dsimp only
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (CurvatureContraction.lineCurvatureContraction b B F a) _ = _
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply]
  simp only [CurvatureContraction.lineCurvatureContraction_sharp b B hB hpos, AntiCovectorMetricDual.antiOneCovector_im_sharp B hpos hBJ a ha,
    map_neg, neg_apply, twoFormBilinear_self, zero_add, smul_eq_mul]
  rw [twoFormBilinear_swap F (Complex.I • _) _]
  ring

theorem lineCurvatureAction_pair (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 a) :
    let r := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear a))
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B (CurvatureContraction.lineCurvatureAction b B F a) a).re =
      2 * (Complex.I * F ![r, Complex.I • r]).re := by
  rw [antiOneCovector_metric_pair b B hB hpos hBJ _ a (lineCurvatureAction_anti b B F a) ha,
    lineCurvatureAction_real_dual b B hB hpos hBJ F a ha, AntiTwoFormCoefficients.twoFormBilinear_apply]

theorem lineCurvatureAction_lower_bound (F : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 a) (c : ℝ)
    (hF : ∀ v : E, c * B v v ≤ (Complex.I * F ![v, Complex.I • v]).re) :
    c * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re ≤
      (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B (CurvatureContraction.lineCurvatureAction b B F a) a).re := by
  rw [lineCurvatureAction_pair b B hB hpos hBJ F a ha,
    AntiCovectorMetricDual.antiOneCovector_metric_norm B hpos hBJ a ha b hB]
  have h := hF (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (Complex.reCLM.comp (AntiOneFormCoordinates.oneFormLinear a)))
  nlinarith

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvaturePair
