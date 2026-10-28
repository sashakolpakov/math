import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RealBasis
import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts
import OAI.Analysis.HodgeTheory.Decomposition.CovectorPair

/-! # Complex Covector -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ComplexCovector.CM.Construction

noncomputable section

section

/-! The intrinsic real-covector metric in complex orthonormal coordinates,
including the factor two and orthogonality of the two one-form types. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype ι]

theorem covectorInner_paired_basis (b : OrthonormalBasis ι ℂ E) (f g : E →ₗ[ℝ] ℂ) :
    Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner f g =
      ∑ i, (star (f (b i)) * g (b i) + star (f (Complex.I • b i)) * g (Complex.I • b i)) := by
  rw [Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner_eq_basis (RealBasis.CM.Construction.complexRealOrthonormalBasis b)]
  simp only [Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorBasisPair, OrthonormalBasis.coe_toBasis,
    Fintype.sum_prod_type, Fin.sum_univ_two,
    RealBasis.CM.Construction.complexRealOrthonormalBasis_zero, RealBasis.CM.Construction.complexRealOrthonormalBasis_one, Finset.sum_add_distrib]

theorem covectorInner_holomorphic_basis (b : OrthonormalBasis ι ℂ E) (f g : E →ₗ[ℝ] ℂ)
    (hf : ∀ u, f (Complex.I • u) = Complex.I * f u)
    (hg : ∀ u, g (Complex.I • u) = Complex.I * g u) :
    Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner f g = 2 * ∑ i, star (f (b i)) * g (b i) := by
  rw [covectorInner_paired_basis b, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hg]
  simp only [star_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem covectorInner_antiholomorphic_basis (b : OrthonormalBasis ι ℂ E) (f g : E →ₗ[ℝ] ℂ)
    (hf : ∀ u, f (Complex.I • u) = -Complex.I * f u)
    (hg : ∀ u, g (Complex.I • u) = -Complex.I * g u) :
    Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner f g = 2 * ∑ i, star (f (b i)) * g (b i) := by
  rw [covectorInner_paired_basis b, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hg]
  simp only [star_mul, star_neg, Complex.star_def, Complex.conj_I, neg_neg]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem covectorInner_opposite_types (b : OrthonormalBasis ι ℂ E) (f g : E →ₗ[ℝ] ℂ)
    (hf : ∀ u, f (Complex.I • u) = Complex.I * f u)
    (hg : ∀ u, g (Complex.I • u) = -Complex.I * g u) :
    Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner f g = 0 := by
  rw [covectorInner_paired_basis b]
  apply Finset.sum_eq_zero
  intro i _
  rw [hf, hg]
  simp only [star_mul, Complex.star_def, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem covectorInner_holomorphic_left (b : OrthonormalBasis ι ℂ E)
    (f : E →ₗ[ℝ] ℂ) (g : E →L[ℝ] ℂ)
    (hf : ∀ u, f (Complex.I • u) = Complex.I * f u) :
    Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner f g.toLinearMap =
      2 * ∑ i, star (f (b i)) * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ g (b i) := by
  rw [covectorInner_paired_basis b, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf]
  simp only [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply, smul_eq_mul, star_mul, Complex.star_def, Complex.conj_I]
  change starRingEnd ℂ (f (b i)) * g (b i) +
    (starRingEnd ℂ (f (b i)) * -Complex.I) * g (Complex.I • b i) =
    2 * (starRingEnd ℂ (f (b i)) * ((1 / 2 : ℂ) * (g (b i) - Complex.I * g (Complex.I • b i))))
  ring

end

section

/-! The complex metric-dual frame gives the actual inverse-Hermitian
coefficient formula for holomorphic one-form pairings. -/

open scoped ComplexOrder

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Fintype ι] [DecidableEq ι]

def complexInverseGramFrame (b : Module.Basis ι ℂ E) (i : ι) : E :=
  ∑ j, star ((Matrix.gram ℂ b)⁻¹ i j) • b j

theorem complexInverseGramFrame_dual (b : Module.Basis ι ℂ E) (i j : ι) :
    inner ℂ (complexInverseGramFrame b i) (b j) = if i = j then 1 else 0 := by
  have hd : IsUnit (Matrix.gram ℂ b).det :=
    isUnit_iff_ne_zero.mpr (Matrix.posDef_gram_of_linearIndependent b.linearIndependent).det_pos.ne'
  have h := congrArg (fun A : Matrix ι ι ℂ => A i j) (Matrix.nonsing_inv_mul (Matrix.gram ℂ b) hd)
  simpa only [complexInverseGramFrame, sum_inner, inner_smul_left, ← Complex.star_def,
    star_star, Matrix.mul_apply, Matrix.gram_apply, Matrix.one_apply] using h

theorem complexInverseGramFrame_coordinates (b : Module.Basis ι ℂ E) (x : E) (i : ι) :
    inner ℂ (complexInverseGramFrame b i) x = b.repr x i := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [inner_sum, inner_smul_right, complexInverseGramFrame_dual]
  simp

theorem complexInverseGramFrame_inner (b : Module.Basis ι ℂ E) (i j : ι) :
    inner ℂ (complexInverseGramFrame b i) (complexInverseGramFrame b j) =
      (Matrix.gram ℂ b)⁻¹ i j := by
  conv_lhs => rhs; rw [complexInverseGramFrame]
  simp only [inner_sum, inner_smul_right, complexInverseGramFrame_dual]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact (Matrix.isHermitian_gram ℂ b).inv.apply i j

theorem complex_covector_dual_frame_expansion (b : Module.Basis ι ℂ E)
    (f : E →ₗ[ℂ] ℂ) (x : E) :
    f x = ∑ i, inner ℂ (complexInverseGramFrame b i) x * f (b i) := by
  simp_rw [complexInverseGramFrame_coordinates]
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, smul_eq_mul]

variable [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem covectorInner_holomorphic_inverse_gram (b : Module.Basis ι ℂ E)
    (f g : E →ₗ[ℂ] ℂ) :
    Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner (f.restrictScalars ℝ) (g.restrictScalars ℝ) =
      2 * ∑ j, ∑ k, star (f (b k)) * (Matrix.gram ℂ b)⁻¹ j k * g (b j) := by
  let : FiniteDimensional ℂ E := b.finiteDimensional_of_finite
  let c := stdOrthonormalBasis ℂ E
  rw [covectorInner_holomorphic_basis c _ _
    (fun u => by simpa only [LinearMap.restrictScalars_apply, smul_eq_mul] using f.map_smul Complex.I u)
    (fun u => by simpa only [LinearMap.restrictScalars_apply, smul_eq_mul] using g.map_smul Complex.I u)]
  congr 1
  have hsum (j k : ι) :
      (∑ l, star (inner ℂ (complexInverseGramFrame b k) (c l)) *
        inner ℂ (complexInverseGramFrame b j) (c l)) = (Matrix.gram ℂ b)⁻¹ j k := by
    simp only [Complex.star_def, inner_conj_symm]
    rw [show (∑ l, inner ℂ (c l) (complexInverseGramFrame b k) *
        inner ℂ (complexInverseGramFrame b j) (c l)) =
        ∑ l, inner ℂ (complexInverseGramFrame b j) (c l) *
          inner ℂ (c l) (complexInverseGramFrame b k) from
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
    rw [c.sum_inner_mul_inner, complexInverseGramFrame_inner]
  change (∑ l, star (f (c l)) * g (c l)) = _
  conv_lhs =>
    enter [2, l]
    rw [complex_covector_dual_frame_expansion b f, complex_covector_dual_frame_expansion b g]
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← hsum j k, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

end

/-! The holomorphic projection of an arbitrary real covector, with its
complex-linear structure and exact intrinsic pairing. -/

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]

def holomorphicCovectorProjection (D : E →L[ℝ] ℂ) : E →L[ℂ] ℂ where
  toFun := Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ D
  map_add' := (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ D).map_add
  map_smul' := fun z u => by
    simpa only [RingHom.id_apply] using Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply_smul E ℂ D z u
  cont := (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E ℂ D).continuous

theorem holomorphicCovectorProjection_apply (D : E →L[ℝ] ℂ) (u : E) :
    holomorphicCovectorProjection D u = (1 / 2 : ℂ) * (D u - Complex.I * D (Complex.I • u)) := rfl

theorem holomorphicCovectorProjection_comp (D : F →L[ℝ] ℂ) (T : E →L[ℂ] F) :
    holomorphicCovectorProjection (D.comp (T.restrictScalars ℝ)) =
      (holomorphicCovectorProjection D).comp T := by
  ext u
  change (1 / 2 : ℂ) * (D (T u) - Complex.I * D (T (Complex.I • u))) =
    (1 / 2 : ℂ) * (D (T u) - Complex.I * D (Complex.I • T u))
  rw [map_smul]

end

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Fintype ι]

theorem covectorInner_holomorphic_projection (b : OrthonormalBasis ι ℂ E)
    (f : E →L[ℂ] ℂ) (g : E →L[ℝ] ℂ) :
    Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner (f.toLinearMap.restrictScalars ℝ) g.toLinearMap =
      Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner (f.toLinearMap.restrictScalars ℝ)
        ((holomorphicCovectorProjection g).toLinearMap.restrictScalars ℝ) := by
  have hf (u : E) : (f.toLinearMap.restrictScalars ℝ) (Complex.I • u) =
      Complex.I * (f.toLinearMap.restrictScalars ℝ) u := by
    change f (Complex.I • u) = Complex.I * f u
    exact f.map_smul Complex.I u
  have hg (u : E) : ((holomorphicCovectorProjection g).toLinearMap.restrictScalars ℝ) (Complex.I • u) =
      Complex.I * ((holomorphicCovectorProjection g).toLinearMap.restrictScalars ℝ) u := by
    change holomorphicCovectorProjection g (Complex.I • u) = Complex.I * holomorphicCovectorProjection g u
    exact (holomorphicCovectorProjection g).map_smul Complex.I u
  rw [covectorInner_holomorphic_left b _ g hf, covectorInner_holomorphic_basis b _ _ hf hg]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ComplexCovector.CM.Construction
