import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition
import OAI.AlgebraicGeometry.ComplexMultiplication.ScalarDescent

/-! # Embedding Coefficient Field -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Embedding bases over a finite coefficient field

If a subfield of `ℂ` contains every conjugate of the acting number field,
the normalized complex embedding basis is already defined over that
coefficient field. The comparison uses the actual inclusion of tensor
coefficients into `ℂ`.
-/

open scoped TensorProduct Classical

variable (K : IntermediateField ℚ ℂ)

/-- Include a tensor's scalar coefficients in `ℂ`, fixing its rational factor. -/
def EmbeddingCoefficientField.CM.coefficientInclusion (U : Type*) [AddCommGroup U] [Module ℚ U] :
    K ⊗[ℚ] U →ₗ[ℚ] WeightOne.CM.Complexification U :=
  TensorProduct.map K.val.toLinearMap LinearMap.id

@[simp]
theorem EmbeddingCoefficientField.CM.coefficientInclusion_tmul {U : Type*} [AddCommGroup U] [Module ℚ U]
    (a : K) (u : U) : EmbeddingCoefficientField.CM.coefficientInclusion K U (a ⊗ₜ[ℚ] u) = (a : ℂ) ⊗ₜ[ℚ] u := rfl

theorem EmbeddingCoefficientField.CM.coefficientInclusion_smul {U : Type*} [AddCommGroup U] [Module ℚ U]
    (a : K) (x : K ⊗[ℚ] U) :
    EmbeddingCoefficientField.CM.coefficientInclusion K U (a • x) = (a : ℂ) • EmbeddingCoefficientField.CM.coefficientInclusion K U x := by
  induction x using TensorProduct.inductionOn with
  | tmul b u => simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- A rational linear map commutes with inclusion of coefficient fields. -/
theorem EmbeddingCoefficientField.CM.coefficientInclusion_baseChange {U V : Type*}
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (f : U →ₗ[ℚ] V) (x : K ⊗[ℚ] U) :
    EmbeddingCoefficientField.CM.coefficientInclusion K V (f.baseChange K x) =
      f.baseChange ℂ (EmbeddingCoefficientField.CM.coefficientInclusion K U x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a u => rfl
  | add x y hx hy => simp [hx, hy]

/-- Scalar conjugation commutes with the scalar extension of a rational map. -/
theorem EmbeddingCoefficientField.CM.scalarConjugate_baseChange {U V : Type*}
    [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (g : Gal(K/ℚ)) (f : U →ₗ[ℚ] V) (x : K ⊗[ℚ] U) :
    ScalarDescent.CM.scalarConjugate ℚ K V g (f.baseChange K x) =
      f.baseChange K (ScalarDescent.CM.scalarConjugate ℚ K U g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a u => rfl
  | add x y hx hy => simp [hx, hy]

variable (E : Type*) [Field E] [Algebra ℚ E]
variable (hK : ∀ σ : E →ₐ[ℚ] ℂ, σ.fieldRange ≤ K)

/-- A complex embedding with all its values regarded as coefficient-field elements. -/
def EmbeddingCoefficientField.CM.coefficientEmbedding (σ : E →ₐ[ℚ] ℂ) : E →ₐ[ℚ] K :=
  σ.codRestrict K.toSubalgebra (fun x => hK σ ⟨x, rfl⟩)

@[simp]
theorem EmbeddingCoefficientField.CM.coefficientEmbedding_coe (σ : E →ₐ[ℚ] ℂ) (x : E) :
    (EmbeddingCoefficientField.CM.coefficientEmbedding K E hK σ x : ℂ) = σ x := rfl

theorem EmbeddingCoefficientField.CM.coefficientEmbedding_injective : Function.Injective (EmbeddingCoefficientField.CM.coefficientEmbedding K E hK) := by
  intro σ τ h
  ext x
  exact congrArg (fun f : E →ₐ[ℚ] K => (f x : ℂ)) h

/-- Apply a coefficient-field automorphism to the values of a complex embedding. -/
def EmbeddingCoefficientField.CM.galoisCoefficientEmbedding (g : Gal(K/ℚ)) (σ : E →ₐ[ℚ] ℂ) : E →ₐ[ℚ] ℂ :=
  K.val.comp (g.toAlgHom.comp (EmbeddingCoefficientField.CM.coefficientEmbedding K E hK σ))

@[simp]
theorem EmbeddingCoefficientField.CM.coefficientEmbedding_galois (g : Gal(K/ℚ)) (σ : E →ₐ[ℚ] ℂ) (x : E) :
    EmbeddingCoefficientField.CM.coefficientEmbedding K E hK (EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g σ) x =
      g (EmbeddingCoefficientField.CM.coefficientEmbedding K E hK σ x) := by
  apply Subtype.ext
  rfl

@[simp]
theorem EmbeddingCoefficientField.CM.galoisCoefficientEmbedding_one (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK 1 σ = σ := by
  ext x
  rfl

theorem EmbeddingCoefficientField.CM.galoisCoefficientEmbedding_mul (g h : Gal(K/ℚ)) (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK (g * h) σ =
      EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g (EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK h σ) := by
  ext x
  change (g (h (EmbeddingCoefficientField.CM.coefficientEmbedding K E hK σ x)) : ℂ) =
    (g (EmbeddingCoefficientField.CM.coefficientEmbedding K E hK (EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK h σ) x) : ℂ)
  rw [EmbeddingCoefficientField.CM.coefficientEmbedding_galois]

/-- Changing scalar coefficients permutes the original embedding set. -/
def EmbeddingCoefficientField.CM.galoisCoefficientEmbeddingEquiv (g : Gal(K/ℚ)) : (E →ₐ[ℚ] ℂ) ≃ (E →ₐ[ℚ] ℂ) where
  toFun := EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g
  invFun := EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g⁻¹
  left_inv σ := by rw [← EmbeddingCoefficientField.CM.galoisCoefficientEmbedding_mul, inv_mul_cancel, EmbeddingCoefficientField.CM.galoisCoefficientEmbedding_one]
  right_inv σ := by rw [← EmbeddingCoefficientField.CM.galoisCoefficientEmbedding_mul, mul_inv_cancel, EmbeddingCoefficientField.CM.galoisCoefficientEmbedding_one]

variable [NumberField E]

/-- All restricted embeddings form a basis of the coefficient-valued rational dual. -/
def EmbeddingCoefficientField.CM.coefficientEmbeddingDualBasis : Module.Basis (E →ₐ[ℚ] ℂ) K (E →ₗ[ℚ] K) :=
  basisOfLinearIndependentOfCardEqFinrank' _
    ((linearIndependent_algHom_toLinearMap ℚ E K).comp _
      (EmbeddingCoefficientField.CM.coefficientEmbedding_injective K E hK))
    (by rw [AlgHom.card, Module.finrank_linearMap_self])

@[simp]
theorem EmbeddingCoefficientField.CM.coefficientEmbeddingDualBasis_apply (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingCoefficientField.CM.coefficientEmbeddingDualBasis K E hK σ = (EmbeddingCoefficientField.CM.coefficientEmbedding K E hK σ).toLinearMap := by
  simp [EmbeddingCoefficientField.CM.coefficientEmbeddingDualBasis]

/-- The coefficient-field splitting is obtained by dualizing the embedding basis. -/
def EmbeddingCoefficientField.CM.coefficientFieldEquiv : K ⊗[ℚ] E ≃ₗ[K] ((E →ₐ[ℚ] ℂ) → K) :=
  (Module.evalEquiv K (K ⊗[ℚ] E)).trans
    ((EmbeddingCoefficientField.CM.coefficientEmbeddingDualBasis K E hK).map
      (LinearMap.liftBaseChangeEquiv K)).dualBasis.equivFun

theorem EmbeddingCoefficientField.CM.coefficientFieldEquiv_apply (x : K ⊗[ℚ] E) (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK x σ =
      (EmbeddingCoefficientField.CM.coefficientEmbedding K E hK σ).toLinearMap.liftBaseChange K x := by
  simp [EmbeddingCoefficientField.CM.coefficientFieldEquiv, Module.Basis.dualBasis_equivFun]

@[simp]
theorem EmbeddingCoefficientField.CM.coefficientFieldEquiv_tmul (z : K) (a : E) (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK (z ⊗ₜ[ℚ] a) σ = z * EmbeddingCoefficientField.CM.coefficientEmbedding K E hK σ a := by
  rw [EmbeddingCoefficientField.CM.coefficientFieldEquiv_apply]
  rfl

variable {E}
variable {U : Type*} [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (h : WeightOne.CM.RankOneCMAction E H)

/-- The actual rank-one module splits over any field containing all embedding values. -/
def WeightOne.CM.RankOneCMAction.coefficientEmbeddingEquiv : K ⊗[ℚ] U ≃ₗ[K] ((E →ₐ[ℚ] ℂ) → K) :=
  ((h.equivField.restrictScalars ℚ).baseChange ℚ K _ _).trans
    (EmbeddingCoefficientField.CM.coefficientFieldEquiv K E hK)

@[simp]
theorem WeightOne.CM.RankOneCMAction.coefficientEmbeddingEquiv_tmul (z : K) (u : U) (σ : E →ₐ[ℚ] ℂ) :
    h.coefficientEmbeddingEquiv K hK (z ⊗ₜ[ℚ] u) σ =
      z * EmbeddingCoefficientField.CM.coefficientEmbedding K E hK σ (h.equivField u) := by
  simp [WeightOne.CM.RankOneCMAction.coefficientEmbeddingEquiv]

/-- A normalized embedding basis using only the chosen field's coefficients. -/
def WeightOne.CM.RankOneCMAction.coefficientEmbeddingBasis : Module.Basis (E →ₐ[ℚ] ℂ) K (K ⊗[ℚ] U) :=
  Module.Basis.ofEquivFun (h.coefficientEmbeddingEquiv K hK)

@[simp]
theorem WeightOne.CM.RankOneCMAction.coefficientEmbeddingEquiv_basis (σ : E →ₐ[ℚ] ℂ) :
    h.coefficientEmbeddingEquiv K hK (h.coefficientEmbeddingBasis K hK σ) =
      Pi.single σ 1 := by
  simp [WeightOne.CM.RankOneCMAction.coefficientEmbeddingBasis]

/-- The coefficient comparison agrees with every embedding coordinate. -/
theorem WeightOne.CM.RankOneCMAction.complexEmbeddingEquiv_coefficientInclusion (x : K ⊗[ℚ] U) (σ : E →ₐ[ℚ] ℂ) :
    h.complexEmbeddingEquiv (EmbeddingCoefficientField.CM.coefficientInclusion K U x) σ =
      (h.coefficientEmbeddingEquiv K hK x σ : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | tmul a u => simp
  | add x y hx hy => simp [hx, hy]

/-- Extending the normalized basis to `ℂ` gives the original complex basis exactly. -/
theorem WeightOne.CM.RankOneCMAction.coefficientInclusion_embeddingBasis (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingCoefficientField.CM.coefficientInclusion K U (h.coefficientEmbeddingBasis K hK σ) = h.embeddingBasis σ := by
  apply h.complexEmbeddingEquiv.injective
  ext τ
  rw [h.complexEmbeddingEquiv_coefficientInclusion K hK,
    h.coefficientEmbeddingEquiv_basis K hK, h.complexEmbeddingEquiv_embeddingBasis]
  by_cases he : σ = τ <;> simp [he]

/-- Embedding coordinates transform with the scalar coefficients. -/
theorem WeightOne.CM.RankOneCMAction.coefficientEmbeddingEquiv_scalarConjugate (g : Gal(K/ℚ)) (x : K ⊗[ℚ] U)
    (σ : E →ₐ[ℚ] ℂ) :
    h.coefficientEmbeddingEquiv K hK (ScalarDescent.CM.scalarConjugate ℚ K U g x)
        (EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g σ) =
      g (h.coefficientEmbeddingEquiv K hK x σ) := by
  induction x using TensorProduct.inductionOn with
  | tmul a u => simp
  | add x y hx hy => simp [hx, hy]

/-- Scalar Galois conjugation permutes the normalized basis exactly. -/
theorem WeightOne.CM.RankOneCMAction.scalarConjugate_coefficientEmbeddingBasis (g : Gal(K/ℚ)) (σ : E →ₐ[ℚ] ℂ) :
    ScalarDescent.CM.scalarConjugate ℚ K U g (h.coefficientEmbeddingBasis K hK σ) =
      h.coefficientEmbeddingBasis K hK (EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g σ) := by
  apply (h.coefficientEmbeddingEquiv K hK).injective
  apply funext
  intro τ
  obtain ⟨τ, rfl⟩ := (EmbeddingCoefficientField.CM.galoisCoefficientEmbeddingEquiv K E hK g).surjective τ
  change h.coefficientEmbeddingEquiv K hK
      (ScalarDescent.CM.scalarConjugate ℚ K U g (h.coefficientEmbeddingBasis K hK σ))
        (EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g τ) =
    h.coefficientEmbeddingEquiv K hK
      (h.coefficientEmbeddingBasis K hK (EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g σ))
        (EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g τ)
  rw [h.coefficientEmbeddingEquiv_scalarConjugate K hK,
    h.coefficientEmbeddingEquiv_basis K hK, h.coefficientEmbeddingEquiv_basis K hK]
  by_cases he : σ = τ
  · subst τ
    simp
  · have hne : EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g σ ≠
        EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK g τ :=
      (EmbeddingCoefficientField.CM.galoisCoefficientEmbeddingEquiv K E hK g).injective.ne he
    simp [he, hne]

end

end OAI.AlgebraicGeometry.ComplexMultiplication
