import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ExteriorMetricLowDegree

/-! # Exterior Two Frame -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ExteriorTwoFrame.CM.Construction

noncomputable section

section

/-! Ordered wedges of an orthonormal real basis give the exact
factor-two resolution of the metric on genuine exterior two-vectors. -/

theorem sum_separated_products {ι R : Type*} [Fintype ι] [CommRing R]
    (f g h k : ι → R) :
    (∑ i, ∑ j, (f i * g j) * (h i * k j)) = (∑ i, f i * h i) * ∑ j, g j * k j := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sum_alternating_products {ι R : Type*} [Fintype ι] [CommRing R]
    (f g h k : ι → R) :
    (∑ i, ∑ j, (f i * g j - g i * f j) * (h i * k j - k i * h j)) =
      2 * ((∑ i, f i * h i) * (∑ j, g j * k j) - (∑ i, f i * k i) * ∑ j, g j * h j) := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [sum_separated_products, sum_separated_products, sum_separated_products, sum_separated_products]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def exteriorTwoVector (u v : E) : ⋀[ℝ]^2 E := exteriorPower.ιMulti ℝ 2 ![u, v]

theorem exteriorTwoVector_inner (u v w z : E) :
    inner ℝ (exteriorTwoVector u v) (exteriorTwoVector w z) =
      inner ℝ u w * inner ℝ v z - inner ℝ u z * inner ℝ v w := by
  simp only [exteriorTwoVector, exteriorPower.inner_ιMulti_ιMulti, Matrix.det_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem exteriorTwoVector_frame_pair {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (u v w z : E) :
    (∑ i, ∑ j, inner ℝ (exteriorTwoVector (b i) (b j)) (exteriorTwoVector u v) *
      inner ℝ (exteriorTwoVector (b i) (b j)) (exteriorTwoVector w z)) =
      2 * inner ℝ (exteriorTwoVector u v) (exteriorTwoVector w z) := by
  have hp (a c : E) : (∑ i, inner ℝ (b i) a * inner ℝ (b i) c) = inner ℝ a c := by
    simpa only [real_inner_comm (b _) a] using b.sum_inner_mul_inner a c
  simp only [exteriorTwoVector_inner]
  have hs := sum_alternating_products (fun i => inner ℝ (b i) u) (fun i => inner ℝ (b i) v)
    (fun i => inner ℝ (b i) w) (fun i => inner ℝ (b i) z)
  simp only [hp] at hs
  exact hs

theorem exteriorTwo_frame_resolution {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (x y : ⋀[ℝ]^2 E) :
    (∑ i, ∑ j, inner ℝ (exteriorTwoVector (b i) (b j)) x *
      inner ℝ (exteriorTwoVector (b i) (b j)) y) = 2 * inner ℝ x y := by
  let B : (⋀[ℝ]^2 E) →ₗ[ℝ] (⋀[ℝ]^2 E) →ₗ[ℝ] ℝ :=
    ∑ i, ∑ j, (innerₗ (⋀[ℝ]^2 E) (exteriorTwoVector (b i) (b j))).smulRight
      (innerₗ (⋀[ℝ]^2 E) (exteriorTwoVector (b i) (b j)))
  have hB : B = (2 : ℝ) • innerₗ (⋀[ℝ]^2 E) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
    simp only [LinearMap.compAlternatingMap_apply, B, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.smul_apply, smul_eq_mul, innerₗ_apply_apply]
    change (∑ i, ∑ j, inner ℝ (exteriorTwoVector (b i) (b j)) (exteriorPower.ιMulti ℝ 2 v) *
      inner ℝ (exteriorTwoVector (b i) (b j)) (exteriorPower.ιMulti ℝ 2 w)) =
      2 * inner ℝ (exteriorPower.ιMulti ℝ 2 v) (exteriorPower.ιMulti ℝ 2 w)
    rw [hv, hw]
    exact exteriorTwoVector_frame_pair b _ _ _ _
  simpa only [B, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul,
    innerₗ_apply_apply] using
    congrArg (fun C : (⋀[ℝ]^2 E) →ₗ[ℝ] (⋀[ℝ]^2 E) →ₗ[ℝ] ℝ => C x y) hB

end

/-! The genuine metric on two-forms is one half of the ordered
orthonormal coordinate sum. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem covectorInner_frame {κ : Type*} [Fintype κ] (v : κ → E) (r : ℝ)
    (hv : ∀ x y, (∑ k, inner ℝ (v k) x * inner ℝ (v k) y) = r * inner ℝ x y)
    (f g : E →ₗ[ℝ] ℂ) :
    (∑ k, star (f (v k)) * g (v k)) = (r : ℂ) * Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner f g := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hdelta (j k : Fin (Module.finrank ℝ E)) :
      (∑ i, (inner ℝ (b j) (v i) : ℂ) * (inner ℝ (b k) (v i) : ℂ)) =
        (r : ℂ) * (if j = k then 1 else 0) := by
    have h := congrArg (fun t : ℝ => (t : ℂ)) (hv (b j) (b k))
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, b.inner_eq_ite, apply_ite,
      Complex.ofReal_one, Complex.ofReal_zero, real_inner_comm (v _) (b _)] using h
  rw [Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorInner_eq_basis b, Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.covectorBasisPair]
  simp only [OrthonormalBasis.coe_toBasis]
  conv_lhs =>
    enter [2, i]
    rw [Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.linearCovector_basis_expansion b f (v i),
      Analysis.HodgeTheory.Decomposition.CovectorPair.Constructions.linearCovector_basis_expansion b g (v i)]
  simp only [star_sum, star_mul, Complex.star_def, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  have hterm (k : Fin (Module.finrank ℝ E)) :
      (∑ i, star (f (b k)) * (inner ℝ (b k) (v i) : ℂ) *
        ((inner ℝ (b j) (v i) : ℂ) * g (b j))) =
      (star (f (b k)) * g (b j)) * ((r : ℂ) * (if k = j then 1 else 0)) := by
    rw [← hdelta k j, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [← Complex.star_def, hterm]
  simp [mul_comm]

theorem formMetricPair_two {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f g : Analysis.DifferentialForms.Manifold.Basic.FormValue E 2) :
    (∑ i, ∑ j, star (f ![b i, b j]) * g ![b i, b j]) =
      2 * Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair 2 f g := by
  have hframe (x y : ⋀[ℝ]^2 E) :
      (∑ k : ι × ι, inner ℝ (exteriorTwoVector (b k.1) (b k.2)) x *
        inner ℝ (exteriorTwoVector (b k.1) (b k.2)) y) = 2 * inner ℝ x y := by
    simpa only [Fintype.sum_prod_type] using exteriorTwo_frame_resolution b x y
  have h := covectorInner_frame (fun k : ι × ι => exteriorTwoVector (b k.1) (b k.2)) 2 hframe
    (Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E 2 f) (Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv E 2 g)
  simpa only [Fintype.sum_prod_type, exteriorTwoVector, Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.exteriorCovectorEquiv_apply_ιMulti,
    Complex.ofReal_ofNat, Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair] using h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ExteriorTwoFrame.CM.Construction
