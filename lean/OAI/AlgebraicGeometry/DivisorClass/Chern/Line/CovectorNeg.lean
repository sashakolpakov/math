import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorTypes
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection
import OAI.Analysis.HodgeTheory.Decomposition.MetricCovariantInsertion

/-! # Covector Neg -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.DivisorClass.Chern

/-! Smoothness of the original bundle covariant coefficient fields on their exact frame-chart domains. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem Line.CovectorNeg.lineCovectorConnectionDerivative_smoothOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U : Set E} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A a) U := by
  let L : Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] ℂ →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n := (ContinuousLinearMap.lsmul ℝ ℂ).flip
  have hL : ContDiff ℝ ∞ L := ContinuousLinearMap.contDiff
    (𝕜 := ℝ) (E := Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (F := ℂ →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) L
  exact (Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.covectorConnectionDerivative_smoothOn n G a hU hG ha).add
    ((hL.comp_contDiffOn ha).clm_comp hA)

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovectorConnection_smooth
    (U : TopologicalSpace.Opens V.analyticSpace) (n : ℕ) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : V.analyticSpace) :
    ContDiffOn ℝ ∞
      (Line.ConnectionSymbols.lineCovectorConnectionDerivative n (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension))
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _) := by
  apply Line.CovectorNeg.lineCovectorConnectionDerivative_smoothOn n _ _ _
    (ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen
  · exact (Analysis.HodgeTheory.Decomposition.ProjectiveConnectionSmooth.Constructions.projectiveConnectionCoefficient_smooth V e he).mono (fun _ hz => hz.1)
  · exact (h.projectiveConnectionChart_smooth V e he i).mono (fun _ hz => ⟨hz.1, hz.2.2⟩)
  · exact ConnectionChartDerivative.projectiveOpenChartForm_smooth V e he _ n (a.val i)

end AlgebraicGeometry.DivisorClass.Chern

namespace AlgebraicGeometry.DivisorClass.Chern.Line.CovectorNeg
section

/-! Differentiating contractions of the actual line covector connection, including the inverse-metric derivative. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lineCovectorConnectionDerivative_contraction (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (w : E → E) {x : E}
    (ha : DifferentiableAt ℝ a x) (hw : DifferentiableAt ℝ w x) (v : E) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A (fun y => Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (w y) (a y)) x v =
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (fderiv ℝ w x v + G x v (w x)) (a x) +
        Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (w x) (ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A a x v) := by
  rw [ConnectionSymbols.lineCovectorConnectionDerivative_apply, ConnectionSymbols.lineCovectorConnectionDerivative_apply,
    Analysis.HodgeTheory.Decomposition.CovariantInsertion.Constructions.covectorConnectionDerivative_contraction n G a w ha hw, map_add, ConnectionSymbols.exteriorContraction_complex_smul]
  abel

end Linear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem lineMetricCovariantInsertion (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (ha : DifferentiableAt ℝ a x) (v : E)
    (hG : ∀ p q, B x (G x v p) q + B x p (G x v q) = fderiv ℝ B x v p q)
    (ξ : E →L[ℝ] ℝ) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A (fun y => Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B y) ξ) (a y)) x v =
      -Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (ξ.comp (G x v))) (a x) +
        Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) ξ) (ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A a x v) := by
  rw [ConnectionSymbols.lineCovectorConnectionDerivative_apply, ConnectionSymbols.lineCovectorConnectionDerivative_apply,
    Analysis.HodgeTheory.Decomposition.MetricCovariantInsertion.Constructions.metricCovariantInsertion n B G a hU hB hpos hx ha v hG ξ, map_add, ConnectionSymbols.exteriorContraction_complex_smul]
  abel

end

/-! Differentiating the actual covariant metric trace, with every inverse-metric term retained. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lineCovectorConnectionDerivative_neg (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x v : E) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A (fun y => -a y) x v =
      -ConnectionSymbols.lineCovectorConnectionDerivative n G A a x v := by
  simp only [ConnectionSymbols.lineCovectorConnectionDerivative_apply, Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply,
    fderiv_fun_neg, _root_.neg_apply, map_neg, smul_neg]
  abel

theorem lineCovectorConnectionDerivative_sum {ι : Type*} (s : Finset ι) (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : ι → E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (ha : ∀ i ∈ s, DifferentiableAt ℝ (a i) x) (v : E) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A (fun y => ∑ i ∈ s, a i y) x v =
      ∑ i ∈ s, ConnectionSymbols.lineCovectorConnectionDerivative n G A (a i) x v := by
  simp only [ConnectionSymbols.lineCovectorConnectionDerivative_apply, Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply,
    fderiv_fun_sum ha, _root_.sum_apply, map_sum, Finset.smul_sum,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

end Linear

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem lineCovariantCodifferential_derivative (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (ha : ContDiffOn ℝ ∞ a U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (v : E)
    (hmetric : ∀ p q, B x (G x v p) q + B x p (G x v q) = fderiv ℝ B x v p q) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A (ConnectionSymbols.lineCovariantCodifferential b n B G A a) x v =
      (∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) ((b.coord i).toContinuousLinearMap.comp (G x v)))
        (ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A a x (b i))) -
      ∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)
        (ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A
          (fun y => ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A a y (b i)) x v) := by
  have hd (i : ι) : ContDiffOn ℝ ∞
      (fun y => ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A a y (b i)) U :=
    (lineCovectorConnectionDerivative_smoothOn (n + 1) G A a hU hG hA ha).clm_apply contDiffOn_const
  have hs (i : ι) : DifferentiableAt ℝ
      (fun y => Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B y) (b.coord i).toContinuousLinearMap)
        (ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A a y (b i))) x :=
    ((Analysis.HodgeTheory.Decomposition.CovariantInsertion.Constructions.exteriorContraction_smoothOn n _ _ (hd i)
      ((Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos).clm_apply contDiffOn_const)).contDiffAt
        (hU.mem_nhds hx)).differentiableAt (by simp)
  change ConnectionSymbols.lineCovectorConnectionDerivative n G A
    (fun y => -(∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B y) (b.coord i).toContinuousLinearMap)
      (ConnectionSymbols.lineCovectorConnectionDerivative (n + 1) G A a y (b i)))) x v = _
  rw [lineCovectorConnectionDerivative_neg, lineCovectorConnectionDerivative_sum Finset.univ n G A _ (fun i _ => hs i)]
  simp_rw [lineMetricCovariantInsertion n B G A _ hU hB hpos hx
    (((hd _).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) v hmetric]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

end AlgebraicGeometry.DivisorClass.Chern.Line.CovectorNeg

end

end OAI
