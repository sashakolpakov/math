import OAI.Analysis.HodgeTheory.Decomposition.ExteriorPair
import OAI.Analysis.HodgeTheory.Decomposition.Contraction
import OAI.Analysis.HodgeTheory.Decomposition.MetricCoefficients

/-! # Bilinear Form Metric -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions

noncomputable section

/-! The induced metric on genuine alternating covectors for any positive
real symmetric tangent metric, with its explicit inverse exterior-Gram formula. -/

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def basisExteriorTuple (b : Module.Basis ι ℝ E) (n : ℕ) (s : Set.powersetCard ι n) : Fin n → E :=
  b ∘ Set.powersetCard.ofFinEmbEquiv.symm s

def bilinearExteriorGram (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    Matrix (Set.powersetCard ι n) (Set.powersetCard ι n) ℝ :=
  fun s t => Matrix.det (fun i j : Fin n => B (basisExteriorTuple b n s j) (basisExteriorTuple b n t i))

def bilinearFormMetricPair (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (a c : DifferentialForms.Manifold.Basic.FormValue E n) : ℂ :=
  ∑ s, ∑ t, star (a (basisExteriorTuple b n t)) * ((bilinearExteriorGram b n B)⁻¹ s t : ℂ) *
    c (basisExteriorTuple b n s)

omit [Fintype ι] [LinearOrder ι] in
def positiveMetricCoordinateForm (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u)
    (n : ℕ) (a : DifferentialForms.Manifold.Basic.FormValue E n) : DifferentialForms.Manifold.Basic.FormValue (ExteriorPair.Constructions.RealMetricFiber E (ExteriorPair.Constructions.positiveBilinearCore B hB hpos)) n :=
  a.compContinuousLinearMap (ExteriorPair.Constructions.realMetricFiberContinuousEquiv (ExteriorPair.Constructions.positiveBilinearCore B hB hpos)).toContinuousLinearMap

def positiveMetricExteriorBasis (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) :
    Module.Basis (Set.powersetCard ι n) ℝ (⋀[ℝ]^n (ExteriorPair.Constructions.RealMetricFiber E (ExteriorPair.Constructions.positiveBilinearCore B hB hpos))) :=
  (b.map (ExteriorPair.Constructions.realMetricFiberContinuousEquiv (ExteriorPair.Constructions.positiveBilinearCore B hB hpos)).symm.toLinearEquiv).exteriorPower n

omit [Fintype ι] in
theorem positiveMetricExteriorBasis_gram (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) :
    Matrix.gram ℝ (positiveMetricExteriorBasis b n B hB hpos) = bilinearExteriorGram b n B := by
  ext s t
  simp only [Matrix.gram_apply, positiveMetricExteriorBasis, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.inner_ιMulti_ιMulti]
  apply congrArg Matrix.det
  ext i j
  rfl

theorem bilinearExteriorGram_det_ne_zero (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) :
    (bilinearExteriorGram b n B).det ≠ 0 := by
  rw [← positiveMetricExteriorBasis_gram b n B hB hpos]
  exact (Matrix.posDef_gram_of_linearIndependent (positiveMetricExteriorBasis b n B hB hpos).linearIndependent).det_pos.ne'

omit [Fintype ι] in
theorem positiveMetricCoordinateForm_basis (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u)
    (a : DifferentialForms.Manifold.Basic.FormValue E n) (s : Set.powersetCard ι n) :
    DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv (ExteriorPair.Constructions.RealMetricFiber E (ExteriorPair.Constructions.positiveBilinearCore B hB hpos)) n
      (positiveMetricCoordinateForm B hB hpos n a) (positiveMetricExteriorBasis b n B hB hpos s) =
        a (basisExteriorTuple b n s) := by
  simp only [positiveMetricExteriorBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_apply_ιMulti]
  rfl

theorem bilinearFormMetricPair_eq_intrinsic (b : Module.Basis ι ℝ E) (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v, B u v = B v u) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (a c : DifferentialForms.Manifold.Basic.FormValue E n) :
    bilinearFormMetricPair b n B a c =
      ExteriorPair.Constructions.formMetricPair n (positiveMetricCoordinateForm B hB hpos n a) (positiveMetricCoordinateForm B hB hpos n c) := by
  unfold ExteriorPair.Constructions.formMetricPair
  rw [Contraction.Constructions.covectorInner_inverse_gram (positiveMetricExteriorBasis b n B hB hpos)]
  simp only [positiveMetricExteriorBasis_gram, positiveMetricCoordinateForm_basis]
  rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions
