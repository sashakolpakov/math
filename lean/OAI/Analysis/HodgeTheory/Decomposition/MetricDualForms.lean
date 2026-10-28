import OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential
import OAI.Analysis.HodgeTheory.Decomposition.ExteriorPair

/-! # Metric Dual Forms -/

namespace OAI.Analysis.HodgeTheory.Decomposition.MetricDualForms.Constructions

noncomputable section

/-! Metric-dual decomposable forms. Their pairing is evaluation, and the
exterior symbol is dual to adjoining its metric-dual vector. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def realMetricDualCovector (x : E) : E →ₗ[ℝ] ℂ :=
  Complex.ofRealCLM.toLinearMap.comp (innerₗ E x)

theorem covectorInner_realMetricDual (x : E) (f : E →ₗ[ℝ] ℂ) :
    CovectorPair.Constructions.covectorInner (realMetricDualCovector x) f = f x := by
  let b := stdOrthonormalBasis ℝ E
  change (∑ i, star (inner ℝ x (b i) : ℂ) * f (b i)) = f x
  simp only [Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ∑ i, (inner ℝ (b i) x : ℂ) * f (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun r : ℝ => (r : ℂ) * f (b i)) (real_inner_comm x (b i)).symm
    _ = f x := (CovectorPair.Constructions.linearCovector_basis_expansion b f x).symm

def metricDualExteriorForm (n : ℕ) (x : ⋀[ℝ]^n E) : DifferentialForms.Manifold.Basic.FormValue E n :=
  (DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n).symm (realMetricDualCovector x)

theorem metricDualExteriorForm_pair (n : ℕ) (x : ⋀[ℝ]^n E) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    ExteriorPair.Constructions.formMetricPair n (metricDualExteriorForm n x) a = DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n a x := by
  unfold ExteriorPair.Constructions.formMetricPair metricDualExteriorForm
  rw [LinearEquiv.apply_symm_apply, covectorInner_realMetricDual]

def metricDualTupleForm (n : ℕ) (u : Fin n → E) : DifferentialForms.Manifold.Basic.FormValue E n :=
  metricDualExteriorForm n (exteriorPower.ιMulti ℝ n u)

theorem metricDualTupleForm_pair (n : ℕ) (u : Fin n → E) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    ExteriorPair.Constructions.formMetricPair n (metricDualTupleForm n u) a = a u :=
  (metricDualExteriorForm_pair n _ a).trans (DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_apply_ιMulti E n a u)

theorem metricDualTupleForm_apply (n : ℕ) (u v : Fin n → E) :
    metricDualTupleForm n u v = (((Matrix.of (fun i j : Fin n => inner ℝ (u j) (v i))).det : ℝ) : ℂ) := by
  change (DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E n).symm (realMetricDualCovector (exteriorPower.ιMulti ℝ n u)) v = _
  rw [DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_symm_apply]
  change (inner ℝ (exteriorPower.ιMulti ℝ n u) (exteriorPower.ιMulti ℝ n v) : ℂ) = _
  rw [exteriorPower.inner_ιMulti_ιMulti]

theorem exteriorSymbol_metricDualTuple (n : ℕ) (w : E) (u : Fin n → E) :
    SymbolDifferential.Constructions.exteriorDifferentialSymbol n (innerSL ℝ w) (metricDualTupleForm n u) =
      metricDualTupleForm (n + 1) (Matrix.vecCons w u) := by
  ext v
  rw [SymbolDifferential.Constructions.exteriorDifferentialSymbol_apply, metricDualTupleForm_apply, Matrix.det_succ_column_zero, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [metricDualTupleForm_apply]
  change ((-1 : ℤ) ^ (i : ℕ)) •
    (inner ℝ w (v i) • ((Matrix.det (fun j k : Fin n => inner ℝ (u k) (i.removeNth v j)) : ℝ) : ℂ)) =
      (((-1 : ℝ) ^ (i : ℕ) * inner ℝ w (v i) *
        Matrix.det (fun j k : Fin n => inner ℝ (u k) (i.removeNth v j)) : ℝ) : ℂ)
  simp only [zsmul_eq_mul, Complex.real_smul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  ring

end

end OAI.Analysis.HodgeTheory.Decomposition.MetricDualForms.Constructions
