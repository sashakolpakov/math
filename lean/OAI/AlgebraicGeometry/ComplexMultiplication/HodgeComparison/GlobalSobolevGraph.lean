import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLp
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Sequences

/-! # Global Sobolev Graph -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSobolevGraph.CM.Construction

noncomputable section

/-! Completion of the graph of the actual smooth exterior derivative in
global metric L2. Its two projections satisfy the exact graph inner product. -/

open _root_.MeasureTheory Set Filter
open scoped _root_.Topology

variable {ι : Type*} [Fintype ι]

abbrev varietySobolevAmbient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (ι : Type*) [Fintype ι] :=
  WithLp 2 (Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) × Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V))

def varietySmoothGraphMap (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ] varietySobolevAmbient V ι :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm.toLinearEquiv.toLinearMap.comp
    ((GlobalLp.CM.Construction.varietySmoothScalarL2 V).prod (GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b))

def varietySobolevGraph (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) : Submodule ℂ (varietySobolevAmbient V ι) :=
  (varietySmoothGraphMap V C b).range.topologicalClosure

instance varietySobolevGraph_complete (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) : CompleteSpace (varietySobolevGraph V C b) :=
  (varietySmoothGraphMap V C b).range.isClosed_topologicalClosure.completeSpace_coe

instance varietySobolevGraph_realInner (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) : InnerProductSpace ℝ (varietySobolevGraph V C b) :=
  InnerProductSpace.complexToReal

def varietySobolevFunction (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    varietySobolevGraph V C b →L[ℂ] Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  (WithLp.fstL 2 ℂ _ _).comp (varietySobolevGraph V C b).subtypeL

def varietySobolevDerivative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    varietySobolevGraph V C b →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V) :=
  (WithLp.sndL 2 ℂ _ _).comp (varietySobolevGraph V C b).subtypeL

def varietySmoothToSobolev (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ] varietySobolevGraph V C b :=
  (varietySmoothGraphMap V C b).codRestrict (varietySobolevGraph V C b)
    (fun f => (varietySmoothGraphMap V C b).range.le_topologicalClosure ⟨f, rfl⟩)

theorem varietySobolevFunction_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (f : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    varietySobolevFunction V C b (varietySmoothToSobolev V C b f) = GlobalLp.CM.Construction.varietySmoothScalarL2 V f := rfl

theorem varietySobolevDerivative_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (f : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0) :
    varietySobolevDerivative V C b (varietySmoothToSobolev V C b f) =
      GlobalLp.CM.Construction.varietyOneFormL2 V C b (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) := rfl

theorem varietySobolevGraph_inner (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (u v : varietySobolevGraph V C b) :
    inner ℂ u v = inner ℂ (varietySobolevFunction V C b u) (varietySobolevFunction V C b v) +
      inner ℂ (varietySobolevDerivative V C b u) (varietySobolevDerivative V C b v) := rfl

theorem varietySobolevGraph_real_inner (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (u v : varietySobolevGraph V C b) :
    inner ℝ u v = inner ℝ (varietySobolevFunction V C b u) (varietySobolevFunction V C b v) +
      inner ℝ (varietySobolevDerivative V C b u) (varietySobolevDerivative V C b v) := by
  have hJ (x y : Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) : inner ℝ x y = (inner ℂ x y).re := by
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
    exact (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) x y).symm
  have hD (x y : Lp (EuclideanSpace ℂ ι) 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V)) :
      inner ℝ x y = (inner ℂ x y).re := by
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
    exact (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) x y).symm
  rw [hJ, hD]
  exact (congrArg Complex.re (varietySobolevGraph_inner V C b u v)).trans (Complex.add_re _ _)

theorem varietySobolevGraph_norm_sq (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (u : varietySobolevGraph V C b) :
    ‖u‖ ^ 2 = ‖varietySobolevFunction V C b u‖ ^ 2 + ‖varietySobolevDerivative V C b u‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using varietySobolevGraph_real_inner V C b u u

theorem varietySmoothToSobolev_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    Function.Injective (varietySmoothToSobolev V C b) := by
  intro f g h
  exact GlobalLp.CM.Construction.varietySmoothScalarL2_injective V (congrArg (varietySobolevFunction V C b) h)

theorem varietySmoothToSobolev_dense (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V)
    (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :
    DenseRange (varietySmoothToSobolev V C b) := by
  intro u
  have hu : u.val ∈ closure (Set.range (varietySmoothGraphMap V C b)) := u.property
  obtain ⟨s, hs, hsu⟩ := mem_closure_iff_seq_limit.mp hu
  choose f hf using hs
  have heq : s = fun n => varietySmoothGraphMap V C b (f n) := funext (fun n => (hf n).symm)
  rw [heq] at hsu
  exact mem_closure_iff_seq_limit.mpr
    ⟨(fun n => varietySmoothToSobolev V C b (f n)), (fun n => ⟨f n, rfl⟩), tendsto_subtype_rng.mpr hsu⟩

/-- Every completed graph element is approached by actual smooth functions
and their actual exterior derivatives, simultaneously in L2. -/
theorem varietySobolevGraph_smooth_approximation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (C : CompactMetricCover.CM.Construction.CompactMetricChartCover V) (b : OrthonormalBasis ι ℝ (EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (u : varietySobolevGraph V C b) :
    ∃ f : ℕ → OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
      Tendsto (fun n => GlobalLp.CM.Construction.varietySmoothScalarL2 V (f n)) atTop (𝓝 (varietySobolevFunction V C b u)) ∧
      Tendsto (fun n => GlobalLp.CM.Construction.varietySmoothDifferentialL2 V C b (f n)) atTop
        (𝓝 (varietySobolevDerivative V C b u)) := by
  have hu : u.val ∈ closure (Set.range (varietySmoothGraphMap V C b)) := u.property
  obtain ⟨s, hs, hsu⟩ := mem_closure_iff_seq_limit.mp hu
  choose f hf using hs
  have heq : s = fun n => varietySmoothGraphMap V C b (f n) := funext (fun n => (hf n).symm)
  rw [heq] at hsu
  exact ⟨f, ((WithLp.fstL 2 ℂ _ _).continuous.tendsto u.val).comp hsu,
    ((WithLp.sndL 2 ℂ _ _).continuous.tendsto u.val).comp hsu⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSobolevGraph.CM.Construction
