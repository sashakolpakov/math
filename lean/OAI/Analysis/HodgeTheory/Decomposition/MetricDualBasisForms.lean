import OAI.Analysis.HodgeTheory.Decomposition.MetricDualForms
import OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric
import OAI.Analysis.HodgeTheory.Decomposition.Form

/-! # Metric Dual Basis Forms -/

namespace OAI.Analysis.HodgeTheory.Decomposition.MetricDualBasisForms.Constructions

noncomputable section

/-! The metric-dual decomposable forms of an orthonormal basis span all
genuine complex-valued alternating covectors. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem metricDualTupleForm_apply_inner (n : ℕ) (u v : Fin n → E) :
    MetricDualForms.Constructions.metricDualTupleForm n u v = (inner ℝ (exteriorPower.ιMulti ℝ n u) (exteriorPower.ιMulti ℝ n v) : ℂ) :=
  DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_symm_apply E n _ v

theorem formMetricPair_sum_left {κ : Type*} [Fintype κ] (n : ℕ) (a : κ → DifferentialForms.Manifold.Basic.FormValue E n) (c : DifferentialForms.Manifold.Basic.FormValue E n) :
    ExteriorPair.Constructions.formMetricPair n (∑ i, a i) c = ∑ i, ExteriorPair.Constructions.formMetricPair n (a i) c := by
  unfold ExteriorPair.Constructions.formMetricPair CovectorPair.Constructions.covectorInner CovectorPair.Constructions.covectorBasisPair
  simp only [map_sum, LinearMap.sum_apply, star_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem orthonormalExteriorBasis_apply (b : OrthonormalBasis ι ℝ E) (n : ℕ) (s : Set.powersetCard ι n) :
    b.exteriorPower n s = exteriorPower.ιMulti ℝ n (BilinearFormMetric.Constructions.basisExteriorTuple b.toBasis n s) := by
  change (b.exteriorPower n).toBasis s = _
  rw [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply]
  rfl

theorem metricDualTuple_basis_expansion (b : OrthonormalBasis ι ℝ E) (n : ℕ) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    a = ∑ s : Set.powersetCard ι n,
      a (BilinearFormMetric.Constructions.basisExteriorTuple b.toBasis n s) • MetricDualForms.Constructions.metricDualTupleForm n (BilinearFormMetric.Constructions.basisExteriorTuple b.toBasis n s) := by
  ext v
  have h := CovectorPair.Constructions.linearCovector_basis_expansion (b.exteriorPower n) (DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n a)
    (exteriorPower.ιMulti ℝ n v)
  simp only [orthonormalExteriorBasis_apply, DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_apply_ιMulti] at h
  change a v = MetricCoefficients.Constructions.formEvaluation n v (∑ s : Set.powersetCard ι n,
    a (BilinearFormMetric.Constructions.basisExteriorTuple b.toBasis n s) • MetricDualForms.Constructions.metricDualTupleForm n (BilinearFormMetric.Constructions.basisExteriorTuple b.toBasis n s))
  rw [map_sum]
  change a v = ∑ s : Set.powersetCard ι n,
    a (BilinearFormMetric.Constructions.basisExteriorTuple b.toBasis n s) * MetricDualForms.Constructions.metricDualTupleForm n (BilinearFormMetric.Constructions.basisExteriorTuple b.toBasis n s) v
  simp_rw [metricDualTupleForm_apply_inner]
  simpa only [mul_comm] using h

end

end OAI.Analysis.HodgeTheory.Decomposition.MetricDualBasisForms.Constructions
