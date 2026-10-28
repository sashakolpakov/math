import OAI.AlgebraicTopology.FundamentalClass.IntegrationOrientation
import OAI.Analysis.HodgeTheory.Integration
import OAI.Analysis.DifferentialForms.Manifold.Algebra
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Integration -/

namespace OAI.AlgebraicTopology.FundamentalClass.Integration

noncomputable section

/-! Integration: independently defined oriented integration of arbitrary top forms.
Each chart contributes its signed top-form coefficient, multiplied by a
subordinate smooth cutoff and integrated against ordinary Lebesgue measure.
Only the local chart signs enter; the homology class and pairing are absent
from this construction. -/

open Set _root_.MeasureTheory
open OAI.Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
    [T2Space M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] [CompactSpace M]

def chartSignInCoordinates (o : IntegrationOrientation.Orientation d M) (center : M) (y : Fin d → ℝ) : ℂ := by
  classical
  exact if hy : y ∈ (chartAt (Fin d → ℝ) center).target then
    ((o.chartSign center
      ⟨(chartAt (Fin d → ℝ) center).symm y, (chartAt (Fin d → ℝ) center).map_target hy⟩ : ℤ) : ℂ)
  else 0

omit [CompactSpace M] in
theorem chartSignInCoordinates_continuousOn (o : IntegrationOrientation.Orientation d M) (center : M) :
    ContinuousOn (chartSignInCoordinates o center) (chartAt (Fin d → ℝ) center).target := by
  rw [continuousOn_iff_continuous_domRestrict]
  let e := chartAt (Fin d → ℝ) center
  have h := (LocallyConstant.map (fun s : ℤˣ => ((s : ℤ) : ℂ))
    (o.chartSign center)).continuous.comp e.toHomeomorphSourceTarget.symm.continuous
  convert h using 1
  funext y
  simp only [Set.domRestrict_apply, chartSignInCoordinates, dite_eq_left y.property]
  rfl

def topFormIntegrand (o : IntegrationOrientation.Orientation d M) (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition (Fin d → ℝ) M)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (i : D.centers) : (Fin d → ℝ) → ℂ :=
  Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff (chartAt (Fin d → ℝ) i.val) (D.partition i)
    (fun y => chartSignInCoordinates o i.val y *
      form.val.inChart (chartAt (Fin d → ℝ) i.val) y (Pi.basisFun ℝ (Fin d)))

omit [T2Space M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] [CompactSpace M] in
theorem topFormCoefficient_continuousOn
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (center : M) :
    ContinuousOn (fun y => form.val.inChart (chartAt (Fin d → ℝ) center) y
      (Pi.basisFun ℝ (Fin d))) (chartAt (Fin d → ℝ) center).target := by
  have h : ContinuousOn (form.val.inChart (chartAt (Fin d → ℝ) center))
      (chartAt (Fin d → ℝ) center).target := by
    simpa [Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain] using
      (form.smooth (chartAt (Fin d → ℝ) center) (chart_mem_atlas (Fin d → ℝ) center)).continuousOn
  exact (continuous_eval_const (Pi.basisFun ℝ (Fin d) : Fin d → (Fin d → ℝ))).comp_continuousOn h

theorem topFormIntegrand_continuous (o : IntegrationOrientation.Orientation d M)
    (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition (Fin d → ℝ) M)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (i : D.centers) :
    Continuous (topFormIntegrand o D form i) :=
  Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff_continuous _ _ (D.partition i).contMDiff.continuous (D.subordinate i) _
    ((chartSignInCoordinates_continuousOn o i.val).mul
      (topFormCoefficient_continuousOn form i.val))

theorem topFormIntegrand_hasCompactSupport (o : IntegrationOrientation.Orientation d M)
    (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition (Fin d → ℝ) M)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (i : D.centers) :
    HasCompactSupport (topFormIntegrand o D form i) :=
  Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff_hasCompactSupport _ _ (D.subordinate i) _

theorem topFormIntegrand_integrable (o : IntegrationOrientation.Orientation d M)
    (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition (Fin d → ℝ) M)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (i : D.centers) :
    Integrable (topFormIntegrand o D form i) :=
  (topFormIntegrand_continuous o D form i).integrable_of_hasCompactSupport
    (topFormIntegrand_hasCompactSupport o D form i)

omit [CompactSpace M] in
theorem topFormIntegrand_add (o : IntegrationOrientation.Orientation d M)
    (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition (Fin d → ℝ) M)
    (form other : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (i : D.centers) :
    topFormIntegrand o D (form + other) i =
      topFormIntegrand o D form i + topFormIntegrand o D other i := by
  ext y
  by_cases hy : y ∈ (chartAt (Fin d → ℝ) i.val).target
  · simp [topFormIntegrand, Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff, hy, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart, mul_add, smul_add]
  · simp [topFormIntegrand, Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff, hy]

omit [CompactSpace M] in
theorem topFormIntegrand_smul (o : IntegrationOrientation.Orientation d M)
    (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition (Fin d → ℝ) M) (c : ℂ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) (i : D.centers) :
    topFormIntegrand o D (c • form) i = c • topFormIntegrand o D form i := by
  ext y
  by_cases hy : y ∈ (chartAt (Fin d → ℝ) i.val).target
  · simp [topFormIntegrand, Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff, hy, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart,
      smul_eq_mul, mul_left_comm, Algebra.smul_def]
  · simp [topFormIntegrand, Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.chartCutoff, hy]

/-- Integration using a specified finite subordinate smooth partition. -/
def topFormIntegralWith (o : IntegrationOrientation.Orientation d M) (D : Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.FiniteChartPartition (Fin d → ℝ) M) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d →ₗ[ℂ] ℂ where
  toFun form := ∑ i : D.centers, ∫ y, topFormIntegrand o D form i y
  map_add' form other := by
    simp only [topFormIntegrand_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_add (topFormIntegrand_integrable o D form i)
      (topFormIntegrand_integrable o D other i)
  map_smul' c form := by
    simp only [topFormIntegrand_smul, Pi.smul_apply, integral_smul, RingHom.id_apply,
      Finset.smul_sum]

/-- Oriented top-form integration, constructed from Lebesgue integrals in charts. -/
def topFormIntegral (o : IntegrationOrientation.Orientation d M) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d →ₗ[ℂ] ℂ :=
  topFormIntegralWith o (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.canonicalChartPartition (Fin d → ℝ) M)

theorem topFormIntegral_eq_chart_sum (o : IntegrationOrientation.Orientation d M)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) :
    topFormIntegral o form =
      ∑ i : (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.canonicalChartPartition (Fin d → ℝ) M).centers,
        ∫ y, topFormIntegrand o (Analysis.HodgeTheory.Integration.Constructions.PolarizedPairing.canonicalChartPartition (Fin d → ℝ) M) form i y := rfl

end

end OAI.AlgebraicTopology.FundamentalClass.Integration
