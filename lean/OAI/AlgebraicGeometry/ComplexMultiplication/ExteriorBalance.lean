import OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorGaloisBasis

/-! # Exterior Balance -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Rational exterior vectors and orbitwise sign balance

The diagonal balanced subspace is the span of exterior monomials whose
actual degree-one Hodge signs sum to zero. A rational vector in this
subspace has support only on monomials balanced throughout their scalar
Galois orbits. Identifying this exterior subspace with the geometric
`(p,p)` subspace of an abelian variety still requires the exterior
cohomology comparison.
-/

open scoped TensorProduct Classical

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : Decomposition.CM.CMDecomposition H) (n : ℕ)

/-- The complex coefficients are the inclusions of the common-field coefficients. -/
theorem Decomposition.CM.CMDecomposition.complexExteriorEmbeddingBasis_repr_coefficientInclusion
    (x : D.commonCoefficientField ⊗[ℚ] (⋀[ℚ]^n U)) (s : D.ExteriorIndex n) :
    (D.complexExteriorEmbeddingBasis n).repr
        (EmbeddingCoefficientField.CM.coefficientInclusion D.commonCoefficientField (⋀[ℚ]^n U) x) s =
      ((D.exteriorEmbeddingBasis n).repr x s : ℂ) := by
  have hx : EmbeddingCoefficientField.CM.coefficientInclusion D.commonCoefficientField (⋀[ℚ]^n U) x =
      ∑ t, ((D.exteriorEmbeddingBasis n).repr x t : ℂ) • D.complexExteriorEmbeddingBasis n t := by
    conv_lhs => rw [← (D.exteriorEmbeddingBasis n).sum_repr x]
    simp only [map_sum, EmbeddingCoefficientField.CM.coefficientInclusion_smul, D.coefficientInclusion_exteriorEmbeddingBasis]
  rw [hx]
  simp [Finsupp.single_apply]

/-- The signed degree of an exterior monomial at a Galois embedding. -/
def Decomposition.CM.CMDecomposition.exteriorSignSum (s : D.ExteriorIndex n) (g : Gal(D.commonCoefficientField/ℚ)) : ℤ :=
  ∑ j ∈ s.val, SignSwitch.CM.signValue (D.galoisSign j g)

/-- Computing signs on the conjugated subset is the same as moving along the scalar orbit. -/
theorem Decomposition.CM.CMDecomposition.exteriorSignSum_galoisIndex (s : D.ExteriorIndex n)
    (g : Gal(D.commonCoefficientField/ℚ)) :
    D.exteriorSignSum n (D.galoisExteriorIndex n g s) 1 = D.exteriorSignSum n s g := by
  change (∑ j ∈ s.val.map (D.galoisIndexEquiv g).toEmbedding,
    SignSwitch.CM.signValue (D.galoisSign j 1)) = ∑ j ∈ s.val, SignSwitch.CM.signValue (D.galoisSign j g)
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk, D.galoisSign_one]
  rfl

/-- The diagonal exterior subspace selected by equal holomorphic and antiholomorphic counts. -/
def Decomposition.CM.CMDecomposition.balancedExteriorSubspace : Submodule ℂ (WeightOne.CM.Complexification (⋀[ℚ]^n U)) :=
  Submodule.span ℂ ((D.complexExteriorEmbeddingBasis n) ''
    {s | D.exteriorSignSum n s 1 = 0})

/-- The diagonal subspace whose monomials remain balanced throughout their scalar orbits. -/
def Decomposition.CM.CMDecomposition.orbitBalancedExteriorSubspace : Submodule ℂ (WeightOne.CM.Complexification (⋀[ℚ]^n U)) :=
  Submodule.span ℂ ((D.complexExteriorEmbeddingBasis n) ''
    {s | ∀ g, D.exteriorSignSum n s g = 0})

/-- A nonzero monomial coefficient of a rational balanced vector is balanced at every conjugate. -/
theorem Decomposition.CM.CMDecomposition.rational_exterior_support_balanced (u : ⋀[ℚ]^n U)
    (hu : (1 : ℂ) ⊗ₜ[ℚ] u ∈ D.balancedExteriorSubspace n) (s : D.ExteriorIndex n)
    (hs : (D.exteriorEmbeddingBasis n).repr ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u) s ≠ 0)
    (g : Gal(D.commonCoefficientField/ℚ)) : D.exteriorSignSum n s g = 0 := by
  have hg := (D.rational_exterior_coefficient_ne_zero_iff n g u s).mpr hs
  have hc : (D.complexExteriorEmbeddingBasis n).repr ((1 : ℂ) ⊗ₜ[ℚ] u)
      (D.galoisExteriorIndex n g s) ≠ 0 := by
    have he := D.complexExteriorEmbeddingBasis_repr_coefficientInclusion n
      ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u) (D.galoisExteriorIndex n g s)
    simp only [EmbeddingCoefficientField.CM.coefficientInclusion_tmul, IntermediateField.coe_one] at he
    rw [he]
    exact (map_ne_zero_iff D.commonCoefficientField.val D.commonCoefficientField.val.injective).mpr hg
  have hb := (D.complexExteriorEmbeddingBasis n).mem_span_image.mp hu
    (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hc))
  exact (D.exteriorSignSum_galoisIndex n s g) ▸ hb

/-- The scalar expansion of a rational balanced vector uses only orbitwise balanced monomials. -/
theorem Decomposition.CM.CMDecomposition.rational_balanced_mem_orbitBalanced (u : ⋀[ℚ]^n U)
    (hu : (1 : ℂ) ⊗ₜ[ℚ] u ∈ D.balancedExteriorSubspace n) :
    (1 : ℂ) ⊗ₜ[ℚ] u ∈ D.orbitBalancedExteriorSubspace n := by
  apply (D.complexExteriorEmbeddingBasis n).mem_span_image.mpr
  intro s hs g
  have hc := Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hs)
  have he := D.complexExteriorEmbeddingBasis_repr_coefficientInclusion n
    ((1 : D.commonCoefficientField) ⊗ₜ[ℚ] u) s
  simp only [EmbeddingCoefficientField.CM.coefficientInclusion_tmul, IntermediateField.coe_one] at he
  rw [he] at hc
  have hk := (map_ne_zero_iff D.commonCoefficientField.val D.commonCoefficientField.val.injective).mp hc
  exact D.rational_exterior_support_balanced n u hu s hk g

end

end OAI.AlgebraicGeometry.ComplexMultiplication
