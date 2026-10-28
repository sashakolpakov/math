import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ExteriorTwoFrame
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoCoefficient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RealBasis

/-! # Mixed Two Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoMetric.CM.Construction

noncomputable section

/-! The metric on a pure (1,1) two-form pairs exactly with the mixed
coefficient of the other two-form. -/

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def twoFormPairedContribution (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) (u v : E) : ℂ :=
  star (KahlerDifferential.CM.Construction.twoFormBilinear f u v) * KahlerDifferential.CM.Construction.twoFormBilinear g u v +
  star (KahlerDifferential.CM.Construction.twoFormBilinear f u (Complex.I • v)) * KahlerDifferential.CM.Construction.twoFormBilinear g u (Complex.I • v) +
  star (KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) v) * KahlerDifferential.CM.Construction.twoFormBilinear g (Complex.I • u) v +
  star (KahlerDifferential.CM.Construction.twoFormBilinear f (Complex.I • u) (Complex.I • v)) *
    KahlerDifferential.CM.Construction.twoFormBilinear g (Complex.I • u) (Complex.I • v)

theorem mixedTwoCoefficient_pair (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 f) (u v : E) :
    twoFormPairedContribution f g u v = 4 *
      (star (MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient f u v) * MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient g u v +
        star (MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient f v u) * MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient g v u) := by
  rw [twoFormPairedContribution, MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient_type11 f hf,
    MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient_type11 f hf, MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient_apply, MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient_apply,
    MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew f u v, MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew f (Complex.I • u) v,
    MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew g u v, MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew g (Complex.I • u) (Complex.I • v),
    MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew g (Complex.I • u) v, MixedTwoCoefficient.CM.Construction.twoFormBilinear_skew g u (Complex.I • v)]
  simp only [MixedTwoCoefficient.CM.Construction.twoFormBilinear_type11_J f hf, MixedTwoCoefficient.CM.Construction.twoFormBilinear_type11_J_left f hf,
    star_mul, star_sub, star_neg, star_div₀, star_ofNat, star_one, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

end

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype ι]

theorem formMetricPair_two_paired_basis (b : OrthonormalBasis ι ℂ E) (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) :
    (∑ i, ∑ j, twoFormPairedContribution f g (b i) (b j)) =
      2 * Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 2 f g := by
  have h := ExteriorTwoFrame.CM.Construction.formMetricPair_two (RealBasis.CM.Construction.complexRealOrthonormalBasis b) f g
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    RealBasis.CM.Construction.complexRealOrthonormalBasis_zero, RealBasis.CM.Construction.complexRealOrthonormalBasis_one] at h
  rw [← h]
  simp only [twoFormPairedContribution, KahlerDifferential.CM.Construction.twoFormBilinear_apply, Finset.sum_add_distrib]
  ring

theorem formMetricPair_type11_basis (b : OrthonormalBasis ι ℂ E) (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2)
    (hf : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 f) :
    Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 2 f g =
      4 * ∑ i, ∑ j, star (MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient f (b i) (b j)) * MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient g (b i) (b j) := by
  have h := formMetricPair_two_paired_basis b f g
  simp only [mixedTwoCoefficient_pair f g hf, mul_add, Finset.sum_add_distrib] at h
  have hs : (∑ i, ∑ j, 4 * (star (MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient f (b j) (b i)) *
      MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient g (b j) (b i))) =
      ∑ i, ∑ j, 4 * (star (MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient f (b i) (b j)) *
        MixedTwoCoefficient.CM.Construction.mixedTwoCoefficient g (b i) (b j)) := Finset.sum_comm
  rw [hs] at h
  simp only [← Finset.mul_sum] at h
  linear_combination (norm := ring_nf) -h / 2

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoMetric.CM.Construction
