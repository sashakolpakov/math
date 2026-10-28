import OAI.AlgebraicGeometry.ComplexMultiplication.HomBaseChange
import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingCoefficientField

/-! # Map Descent -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.MapDescent.CM

noncomputable section

/-!
# Descent of coefficient-valued Hodge maps

Complex maps must preserve both weight-one types. For a rational map this
condition agrees with the existing `IsHodgeMap` predicate. If every scalar
Galois conjugate of a map over a finite Galois coefficient field preserves
these types, the complex map lies in the complex span of rational Hodge
maps. The conclusion concerns actual linear maps on complexifications.
-/

open scoped TensorProduct Classical

variable (K : IntermediateField ℚ ℂ)
variable {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]

/-- Complex linear maps preserving both weight-one Hodge subspaces. -/
def hodgeHomSubspace (H : WeightOne.CM.WeightOneHodgeStructure U) (J : WeightOne.CM.WeightOneHodgeStructure V) :
    Submodule ℂ (WeightOne.CM.Complexification U →ₗ[ℂ] WeightOne.CM.Complexification V) where
  carrier := {f | (∀ x ∈ H.holomorphic, f x ∈ J.holomorphic) ∧
    ∀ x ∈ H.antiholomorphic, f x ∈ J.antiholomorphic}
  zero_mem' := ⟨fun _ _ => J.holomorphic.zero_mem, fun _ _ => J.antiholomorphic.zero_mem⟩
  add_mem' hf hg := ⟨fun x hx => J.holomorphic.add_mem (hf.1 x hx) (hg.1 x hx),
    fun x hx => J.antiholomorphic.add_mem (hf.2 x hx) (hg.2 x hx)⟩
  smul_mem' a _ hf := ⟨fun x hx => J.holomorphic.smul_mem a (hf.1 x hx),
    fun x hx => J.antiholomorphic.smul_mem a (hf.2 x hx)⟩

/-- For rational maps, preservation of the second type follows from coefficient conjugation. -/
theorem baseChange_mem_hodgeHomSubspace_iff (H : WeightOne.CM.WeightOneHodgeStructure U)
    (J : WeightOne.CM.WeightOneHodgeStructure V) (f : U →ₗ[ℚ] V) :
    f.baseChange ℂ ∈ hodgeHomSubspace H J ↔ WeightOne.CM.IsHodgeMap H J f := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun _ hx => h.map_antiholomorphic hx⟩

variable (U V)

/-- Interpret a coefficient Hom tensor as an actual complex linear map. -/
def complexHomOfCoefficients :
    K ⊗[ℚ] (U →ₗ[ℚ] V) →ₗ[K] (WeightOne.CM.Complexification U →ₗ[ℂ] WeightOne.CM.Complexification V) where
  toFun x := HomBaseChange.CM.homBaseChange ℂ U V (EmbeddingCoefficientField.CM.coefficientInclusion K (U →ₗ[ℚ] V) x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a x := by
    rw [EmbeddingCoefficientField.CM.coefficientInclusion_smul, map_smul]
    rfl

@[simp]
theorem complexHomOfCoefficients_tmul (a : K) (f : U →ₗ[ℚ] V) :
    complexHomOfCoefficients K U V (a ⊗ₜ[ℚ] f) = (a : ℂ) • f.baseChange ℂ := by
  simp only [complexHomOfCoefficients, LinearMap.coe_mk, AddHom.coe_mk,
    EmbeddingCoefficientField.CM.coefficientInclusion_tmul, HomBaseChange.CM.homBaseChange_tmul]

/-- Including coefficients commutes with applying the corresponding coefficient-field map. -/
theorem complexHomOfCoefficients_apply_inclusion (x : K ⊗[ℚ] (U →ₗ[ℚ] V))
    (u : K ⊗[ℚ] U) :
    complexHomOfCoefficients K U V x (EmbeddingCoefficientField.CM.coefficientInclusion K U u) =
      EmbeddingCoefficientField.CM.coefficientInclusion K V (HomBaseChange.CM.homBaseChange K U V x u) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a f =>
    induction u using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul b u => simp [TensorProduct.smul_tmul', smul_eq_mul]

variable {U V}

/-- Coefficient Hom tensors whose actual complex maps preserve both Hodge types. -/
def hodgeHomCoefficientSubspace (H : WeightOne.CM.WeightOneHodgeStructure U)
    (J : WeightOne.CM.WeightOneHodgeStructure V) : Submodule K (K ⊗[ℚ] (U →ₗ[ℚ] V)) :=
  ((hodgeHomSubspace H J).restrictScalars K).comap (complexHomOfCoefficients K U V)

@[simp]
theorem mem_hodgeHomCoefficientSubspace (H : WeightOne.CM.WeightOneHodgeStructure U)
    (J : WeightOne.CM.WeightOneHodgeStructure V) (x : K ⊗[ℚ] (U →ₗ[ℚ] V)) :
    x ∈ hodgeHomCoefficientSubspace K H J ↔
      complexHomOfCoefficients K U V x ∈ hodgeHomSubspace H J := Iff.rfl

/-- Rational points of this coefficient subspace are precisely rational Hodge maps. -/
theorem one_tmul_mem_hodgeHomCoefficientSubspace (H : WeightOne.CM.WeightOneHodgeStructure U)
    (J : WeightOne.CM.WeightOneHodgeStructure V) (f : U →ₗ[ℚ] V) :
    (1 : K) ⊗ₜ[ℚ] f ∈ hodgeHomCoefficientSubspace K H J ↔ WeightOne.CM.IsHodgeMap H J f := by
  rw [mem_hodgeHomCoefficientSubspace, complexHomOfCoefficients_tmul]
  simp only [IntermediateField.coe_one, one_smul, baseChange_mem_hodgeHomSubspace_iff]

/-- The actual complex span of rational Hodge maps. -/
def rationalHodgeMapSpan (H : WeightOne.CM.WeightOneHodgeStructure U) (J : WeightOne.CM.WeightOneHodgeStructure V) :
    Submodule ℂ (WeightOne.CM.Complexification U →ₗ[ℂ] WeightOne.CM.Complexification V) :=
  Submodule.span ℂ {f | ∃ q : U →ₗ[ℚ] V, WeightOne.CM.IsHodgeMap H J q ∧ q.baseChange ℂ = f}

variable [NumberField K] [IsGalois ℚ K]

/-- The scalar-trace descent assertion for Hodge maps in the manuscript. -/
theorem complexHom_mem_rationalHodgeMapSpan_of_conjugates
    (H : WeightOne.CM.WeightOneHodgeStructure U) (J : WeightOne.CM.WeightOneHodgeStructure V)
    (x : K ⊗[ℚ] (U →ₗ[ℚ] V))
    (hx : ∀ g : Gal(K/ℚ),
      complexHomOfCoefficients K U V (ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] V) g x) ∈
        hodgeHomSubspace H J) :
    complexHomOfCoefficients K U V x ∈ rationalHodgeMapSpan H J := by
  have hspan := ScalarDescent.CM.mem_span_baseField_of_conjugates ℚ K (U →ₗ[ℚ] V)
    (hodgeHomCoefficientSubspace K H J) hx
  have hle : Submodule.span K
      {y | ∃ q : U →ₗ[ℚ] V, y = (1 : K) ⊗ₜ[ℚ] q ∧ y ∈ hodgeHomCoefficientSubspace K H J} ≤
      ((rationalHodgeMapSpan H J).restrictScalars K).comap (complexHomOfCoefficients K U V) := by
    apply Submodule.span_le.mpr
    rintro y ⟨q, rfl, hq⟩
    change complexHomOfCoefficients K U V ((1 : K) ⊗ₜ[ℚ] q) ∈ rationalHodgeMapSpan H J
    rw [complexHomOfCoefficients_tmul]
    simp only [IntermediateField.coe_one, one_smul]
    exact Submodule.subset_span ⟨q, (one_tmul_mem_hodgeHomCoefficientSubspace K H J q).mp hq, rfl⟩
  exact hle hspan

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.MapDescent.CM
