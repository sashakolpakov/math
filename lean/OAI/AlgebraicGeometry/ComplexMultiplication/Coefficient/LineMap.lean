import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.MapDescent
import OAI.AlgebraicGeometry.ComplexMultiplication.DecompositionEmbeddingBasis

/-! # Line Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.LineMap.CM

noncomputable section

/-!
# Maps supported on a single pair of embedding lines

The elementary map sends one specified basis vector to another and kills
the remaining source vectors. Its rational Hom coefficient tensor exists
by the canonical Hom comparison. Conjugating coefficients permutes its
source and target indices. Matching Hodge signs along these permutations
will therefore allow descent to rational Hodge maps.
-/

open scoped TensorProduct Classical

section Bases

variable {F X Y ι κ : Type*} [Field F] [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]

/-- Send one basis line to another, with coefficient one, and kill all other source lines. -/
def basisLineMap (b : Module.Basis ι F X) (c : Module.Basis κ F Y) (i : ι) (j : κ) : X →ₗ[F] Y :=
  (b.coord i).smulRight (c j)

@[simp]
theorem basisLineMap_apply (b : Module.Basis ι F X) (c : Module.Basis κ F Y)
    (i : ι) (j : κ) (x : X) : basisLineMap b c i j x = b.repr x i • c j := rfl

@[simp]
theorem basisLineMap_basis (b : Module.Basis ι F X) (c : Module.Basis κ F Y)
    (i k : ι) (j : κ) : basisLineMap b c i j (b k) = if k = i then c j else 0 := by
  simp [basisLineMap_apply, Finsupp.single_apply]

theorem basisLineMap_ne_zero (b : Module.Basis ι F X) (c : Module.Basis κ F Y)
    (i : ι) (j : κ) : basisLineMap b c i j ≠ 0 := by
  intro h
  have he := congrArg (fun f : X →ₗ[F] Y => f (b i)) h
  simp only [basisLineMap_basis, LinearMap.zero_apply] at he
  exact c.ne_zero j he

end Bases

section Coefficients

variable {K U V ι κ : Type*} [Field K] [Algebra ℚ K]
  [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
  [FiniteDimensional ℚ U]

/-- The actual scalar extension of the rational Hom space representing a one-line map. -/
def lineMapTensor (b : Module.Basis ι K (K ⊗[ℚ] U)) (c : Module.Basis κ K (K ⊗[ℚ] V))
    (i : ι) (j : κ) : K ⊗[ℚ] (U →ₗ[ℚ] V) :=
  (HomBaseChange.CM.homBaseChangeEquiv K U V).symm (basisLineMap b c i j)

@[simp]
theorem homBaseChange_lineMapTensor (b : Module.Basis ι K (K ⊗[ℚ] U))
    (c : Module.Basis κ K (K ⊗[ℚ] V)) (i : ι) (j : κ) :
    HomBaseChange.CM.homBaseChange K U V (lineMapTensor b c i j) = basisLineMap b c i j :=
  (HomBaseChange.CM.homBaseChangeEquiv K U V).apply_symm_apply _

/-- Exact scalar Galois covariance of the elementary map's coefficient tensor. -/
theorem scalarConjugate_lineMapTensor (b : Module.Basis ι K (K ⊗[ℚ] U))
    (c : Module.Basis κ K (K ⊗[ℚ] V)) (g : Gal(K/ℚ)) (π : Equiv.Perm ι) (ρ : Equiv.Perm κ)
    (hb : ∀ i, ScalarDescent.CM.scalarConjugate ℚ K U g (b i) = b (π i))
    (hc : ∀ j, ScalarDescent.CM.scalarConjugate ℚ K V g (c j) = c (ρ j)) (i : ι) (j : κ) :
    ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] V) g (lineMapTensor b c i j) =
      lineMapTensor b c (π i) (ρ j) := by
  apply (HomBaseChange.CM.homBaseChangeEquiv K U V).injective
  simp only [HomBaseChange.CM.homBaseChangeEquiv_apply, homBaseChange_lineMapTensor]
  apply b.ext
  intro k
  obtain ⟨k, rfl⟩ := π.surjective k
  rw [← hb k, HomBaseChange.CM.homBaseChange_scalarConjugate, homBaseChange_lineMapTensor, hb k]
  rw [basisLineMap_basis, basisLineMap_basis]
  by_cases hk : k = i
  · simp only [hk, ite_true, hc j]
  · simp only [ite_eq_right hk, ite_eq_right (π.injective.ne hk), map_zero]

end Coefficients

variable {U V ι κ : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]

/-- Matching source and target signs make a one-line map preserve both Hodge types. -/
theorem basisLineMap_mem_hodgeHomSubspace
    (H : WeightOne.CM.WeightOneHodgeStructure U) (J : WeightOne.CM.WeightOneHodgeStructure V)
    (b : Module.Basis ι ℂ (WeightOne.CM.Complexification U)) (c : Module.Basis κ ℂ (WeightOne.CM.Complexification V))
    (s : ι → Bool) (t : κ → Bool)
    (hb : ∀ e, H.signSubspace e = Submodule.span ℂ (b '' {i | s i = e}))
    (hc : ∀ j, c j ∈ J.signSubspace (t j)) (i : ι) (j : κ) (hij : s i = t j) :
    basisLineMap b c i j ∈ Hodge.MapDescent.CM.hodgeHomSubspace H J := by
  have hm (e : Bool) (x : WeightOne.CM.Complexification U) (hx : x ∈ H.signSubspace e) :
      basisLineMap b c i j x ∈ J.signSubspace e := by
    by_cases hz : b.repr x i = 0
    · simp only [basisLineMap_apply, hz, zero_smul]
      exact (J.signSubspace e).zero_mem
    · rw [hb e] at hx
      have he := b.mem_span_image.mp hx (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hz))
      have ht : t j = e := hij.symm.trans he
      rw [basisLineMap_apply, ← ht]
      exact (J.signSubspace (t j)).smul_mem _ (hc j)
  exact ⟨hm true, hm false⟩

variable (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ U]

/-- Including the coefficients of an elementary map gives the corresponding complex map. -/
theorem complexHomOfCoefficients_lineMapTensor
    (b : Module.Basis ι K (K ⊗[ℚ] U)) (c : Module.Basis κ K (K ⊗[ℚ] V))
    (bC : Module.Basis ι ℂ (WeightOne.CM.Complexification U)) (cC : Module.Basis κ ℂ (WeightOne.CM.Complexification V))
    (hb : ∀ i, EmbeddingCoefficientField.CM.coefficientInclusion K U (b i) = bC i)
    (hc : ∀ j, EmbeddingCoefficientField.CM.coefficientInclusion K V (c j) = cC j) (i : ι) (j : κ) :
    Hodge.MapDescent.CM.complexHomOfCoefficients K U V (lineMapTensor b c i j) = basisLineMap bC cC i j := by
  apply bC.ext
  intro k
  rw [← hb k, Hodge.MapDescent.CM.complexHomOfCoefficients_apply_inclusion, homBaseChange_lineMapTensor, hb k]
  rw [basisLineMap_basis, basisLineMap_basis]
  by_cases hk : k = i
  · simp only [hk, ite_true, hc j]
  · simp only [ite_eq_right hk, map_zero]

variable [NumberField K] [IsGalois ℚ K]

/-- A one-line map whose source and target signs agree at every scalar conjugate
is in the complex span of rational Hodge maps. -/
theorem basisLineMap_mem_rationalHodgeMapSpan
    (H : WeightOne.CM.WeightOneHodgeStructure U) (J : WeightOne.CM.WeightOneHodgeStructure V)
    (b : Module.Basis ι K (K ⊗[ℚ] U)) (c : Module.Basis κ K (K ⊗[ℚ] V))
    (bC : Module.Basis ι ℂ (WeightOne.CM.Complexification U)) (cC : Module.Basis κ ℂ (WeightOne.CM.Complexification V))
    (hbC : ∀ i, EmbeddingCoefficientField.CM.coefficientInclusion K U (b i) = bC i)
    (hcC : ∀ j, EmbeddingCoefficientField.CM.coefficientInclusion K V (c j) = cC j)
    (π : Gal(K/ℚ) → Equiv.Perm ι) (ρ : Gal(K/ℚ) → Equiv.Perm κ)
    (hbg : ∀ g i, ScalarDescent.CM.scalarConjugate ℚ K U g (b i) = b (π g i))
    (hcg : ∀ g j, ScalarDescent.CM.scalarConjugate ℚ K V g (c j) = c (ρ g j))
    (s : ι → Bool) (t : κ → Bool)
    (hb : ∀ e, H.signSubspace e = Submodule.span ℂ (bC '' {i | s i = e}))
    (hc : ∀ j, cC j ∈ J.signSubspace (t j)) (i : ι) (j : κ)
    (hs : ∀ g, s (π g i) = t (ρ g j)) :
    basisLineMap bC cC i j ∈ Hodge.MapDescent.CM.rationalHodgeMapSpan H J := by
  rw [← complexHomOfCoefficients_lineMapTensor K b c bC cC hbC hcC i j]
  apply Hodge.MapDescent.CM.complexHom_mem_rationalHodgeMapSpan_of_conjugates K H J
  intro g
  rw [scalarConjugate_lineMapTensor b c g (π g) (ρ g) (hbg g) (hcg g),
    complexHomOfCoefficients_lineMapTensor K b c bC cC hbC hcC]
  exact basisLineMap_mem_hodgeHomSubspace H J bC cC s t hb hc _ _ (hs g)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.LineMap.CM
