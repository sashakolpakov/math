import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionSymbols
import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ConnectionCurvature
import OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms

/-! # Connection Chart Derivative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionChartDerivative

noncomputable section

section

/-! The connection symbols have exactly the chart values of the actual open connection derivative. -/

open _root_.TopologicalSpace _root_.ContinuousAlternatingMap
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem alternation_lineConnectionTerm_one (A a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    alternatizeUncurryFin (Line.ConnectionSymbols.lineConnectionTerm 1 (AntiOneFormCoordinates.oneFormLinear A) a) = AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge A a := by
  ext v
  rw [alternatizeUncurryFin_apply, Fin.sum_univ_two, OneFormWedgeEvaluation.covectorWedge_one_one_apply]
  have h0 : Fin.tail v = (fun _ : Fin 1 => v 1) := by funext i; fin_cases i; rfl
  have h1 : Fin.removeNth (1 : Fin 2) v = (fun _ : Fin 1 => v 0) := by funext i; fin_cases i; rfl
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero, Fin.val_one,
    pow_one, neg_smul, Line.ConnectionSymbols.lineConnectionTerm_apply, ContinuousAlternatingMap.smul_apply,
    AntiOneFormCoordinates.oneFormLinear_apply, smul_eq_mul, h0, h1]
  rfl

variable {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {U : Opens M}

theorem openConnectionDerivativeOne_inChart (A a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U) :
    (Open.ConnectionCurvature.openConnectionDerivativeOne A a).extension.inChart e y =
      Line.ConnectionSymbols.lineExteriorDerivative 1 (fun z => AntiOneFormCoordinates.oneFormLinear (A.extension.inChart e z))
        (a.extension.inChart e) y := by
  rw [Open.ConnectionCurvature.openConnectionDerivativeOne_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add, Pi.add_apply, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_inChart a e he hy,
    Open.ManifoldWedge.openManifoldWedge_inChart A a e hy.2]
  exact congrArg (fun b => extDeriv (a.extension.inChart e) y + b)
    (alternation_lineConnectionTerm_one (A.extension.inChart e y) (a.extension.inChart e y)).symm

end

/-! Actual open bundle-frame forms in the original projective metric's Hilbert coordinates. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (U : Opens V.analyticSpace)

def projectiveOpenChartDomain : Opens (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :=
  ⟨ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ⁻¹' (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set V.analyticModel),
    (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.preimage (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).continuous⟩

theorem projectiveOpenChartDomain_le : projectiveOpenChartDomain V e U ≤ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
  fun _ hz => hz.1

include he

theorem projectiveOpenChartForm_smooth (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n) :
    ContDiffOn ℝ ∞ (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n a.extension) (projectiveOpenChartDomain V e U : Set _) := by
  have hcomp := (a.smooth e he).comp ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ).contDiffOn
    (show Set.MapsTo (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V) (projectiveOpenChartDomain V e U : Set _)
      (Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U : Set _) from fun _ hz => hz)
  exact Analysis.DifferentialForms.Manifold.Alternatization.contDiffOn_alternating_compContinuousLinearMap hcomp contDiffOn_const

theorem projectiveOpenChartForm_d (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ projectiveOpenChartDomain V e U) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (n + 1) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a).extension z =
      extDeriv (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n a.extension) z := by
  have hA := ((a.smooth e he).contDiffAt ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hL : ContDiff ℝ ∞ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V) :=
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ
  have hder (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : fderiv ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V) w =
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ :=
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.fderiv
  have hd := extDeriv_pullback (f := ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V) (x := z)
    hA hL.contDiffAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  simp only [hder] at hd
  change ((Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a).extension.inChart e (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)).compContinuousLinearMap _ = _
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_inChart a e he hz]
  exact hd.symm

omit he in
theorem projectiveOpenChartForm_wedge {p q : ℕ}
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U p) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U q)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ projectiveOpenChartDomain V e U) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e (p + q) (Open.ManifoldWedge.openManifoldWedge a b).extension z =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e p a.extension z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e q b.extension z) := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  rw [Open.ManifoldWedge.openManifoldWedge_inChart a b e hz.2]
  exact (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback _ _ _).symm

theorem projectiveOpenChartForm_connectionOne (A a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 1)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ projectiveOpenChartDomain V e U) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (Open.ConnectionCurvature.openConnectionDerivativeOne A a).extension z =
      Line.ConnectionSymbols.lineExteriorDerivative 1 (fun y => AntiOneFormCoordinates.oneFormLinear (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 A.extension y))
        (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.extension) z := by
  have hadd (b c : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm V.analyticModel U 2) :
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 (b + c).extension z =
        Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 b.extension z + Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 c.extension z := by
    simp only [Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add,
      Pi.add_apply]
    ext v
    rfl
  rw [Open.ConnectionCurvature.openConnectionDerivativeOne_apply, hadd, projectiveOpenChartForm_d V e he U 1 a hz,
    projectiveOpenChartForm_wedge V e U A a hz]
  exact congrArg (fun b => extDeriv (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 a.extension) z + b)
    (alternation_lineConnectionTerm_one _ _).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectionChartDerivative
