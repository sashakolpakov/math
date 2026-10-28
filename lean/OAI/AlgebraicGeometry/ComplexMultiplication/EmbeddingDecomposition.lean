import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Embedding Decomposition -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Complex embedding decomposition of rank-one CM modules

The decomposition is constructed from actual field embeddings. Their linear
independence and the separable extension degree give a basis of the dual;
dualizing gives the canonical evaluation isomorphism on complexification.
No splitting isomorphism or eigenspace dimension is assumed.
-/

open scoped TensorProduct Classical

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]

/-- The complex embeddings of a number field form a basis of its
complex-valued rational-linear dual. -/
def EmbeddingDecomposition.CM.complexEmbeddingBasis : Module.Basis (E →ₐ[ℚ] ℂ) ℂ (E →ₗ[ℚ] ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_algHom_toLinearMap ℚ E ℂ)
    (by rw [AlgHom.card, Module.finrank_linearMap_self])

@[simp]
theorem EmbeddingDecomposition.CM.complexEmbeddingBasis_apply (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.complexEmbeddingBasis E σ = σ.toLinearMap := by
  simp [EmbeddingDecomposition.CM.complexEmbeddingBasis]

/-- Extending each embedding gives the dual basis of the complexification. -/
def EmbeddingDecomposition.CM.complexifiedEmbeddingBasis :
    Module.Basis (E →ₐ[ℚ] ℂ) ℂ (Module.Dual ℂ (WeightOne.CM.Complexification E)) :=
  (EmbeddingDecomposition.CM.complexEmbeddingBasis E).map (LinearMap.liftBaseChangeEquiv ℂ)

@[simp]
theorem EmbeddingDecomposition.CM.complexifiedEmbeddingBasis_apply (σ : E →ₐ[ℚ] ℂ) (x : WeightOne.CM.Complexification E) :
    EmbeddingDecomposition.CM.complexifiedEmbeddingBasis E σ x = σ.toLinearMap.liftBaseChange ℂ x := by
  simp [EmbeddingDecomposition.CM.complexifiedEmbeddingBasis]

/-- Canonical splitting of the complexification into all embedding coordinates. -/
def EmbeddingDecomposition.CM.fieldComplexificationEquiv : WeightOne.CM.Complexification E ≃ₗ[ℂ] ((E →ₐ[ℚ] ℂ) → ℂ) :=
  (Module.evalEquiv ℂ (WeightOne.CM.Complexification E)).trans
    (EmbeddingDecomposition.CM.complexifiedEmbeddingBasis E).dualBasis.equivFun

theorem EmbeddingDecomposition.CM.fieldComplexificationEquiv_apply (x : WeightOne.CM.Complexification E) (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.fieldComplexificationEquiv E x σ = σ.toLinearMap.liftBaseChange ℂ x := by
  simp [EmbeddingDecomposition.CM.fieldComplexificationEquiv, Module.Basis.dualBasis_equivFun]

@[simp]
theorem EmbeddingDecomposition.CM.fieldComplexificationEquiv_tmul (z : ℂ) (a : E) (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.fieldComplexificationEquiv E (z ⊗ₜ[ℚ] a) σ = z * σ a := by
  rw [EmbeddingDecomposition.CM.fieldComplexificationEquiv_apply]
  rfl

/-- The coordinate idempotent for an embedding, as a vector in the actual
complexified field. -/
def EmbeddingDecomposition.CM.embeddingVector (σ : E →ₐ[ℚ] ℂ) : WeightOne.CM.Complexification E :=
  (EmbeddingDecomposition.CM.fieldComplexificationEquiv E).symm (Pi.single σ 1)

@[simp]
theorem EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.fieldComplexificationEquiv E (EmbeddingDecomposition.CM.embeddingVector E σ) = Pi.single σ 1 :=
  (EmbeddingDecomposition.CM.fieldComplexificationEquiv E).apply_symm_apply _

/-- Multiplication by a field element acts diagonally on these coordinates. -/
theorem EmbeddingDecomposition.CM.fieldComplexificationEquiv_scalar (a : E) (x : WeightOne.CM.Complexification E)
    (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.fieldComplexificationEquiv E ((WeightOne.CM.scalarEndomorphism E a).baseChange ℂ x) σ =
      σ a * EmbeddingDecomposition.CM.fieldComplexificationEquiv E x σ := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, mul_add]
  | tmul z b =>
    simp [WeightOne.CM.scalarEndomorphism, mul_left_comm]

/-- Each coordinate vector is an eigenvector for every element of the field. -/
theorem EmbeddingDecomposition.CM.embeddingVector_eigen (a : E) (σ : E →ₐ[ℚ] ℂ) :
    (WeightOne.CM.scalarEndomorphism E a).baseChange ℂ (EmbeddingDecomposition.CM.embeddingVector E σ) =
      σ a • EmbeddingDecomposition.CM.embeddingVector E σ := by
  classical
  apply (EmbeddingDecomposition.CM.fieldComplexificationEquiv E).injective
  ext τ
  rw [EmbeddingDecomposition.CM.fieldComplexificationEquiv_scalar, map_smul,
    EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector]
  by_cases h : σ = τ
  · subst τ
    simp
  · simp [h]

/-- None of the embedding lines is a zero space. -/
theorem EmbeddingDecomposition.CM.embeddingVector_ne_zero (σ : E →ₐ[ℚ] ℂ) : EmbeddingDecomposition.CM.embeddingVector E σ ≠ 0 := by
  intro h
  have he := congrArg (fun x => EmbeddingDecomposition.CM.fieldComplexificationEquiv E x σ) h
  simp at he

/-- The embedding vectors form a basis, not just a family of eigenvectors. -/
def EmbeddingDecomposition.CM.fieldEmbeddingBasis : Module.Basis (E →ₐ[ℚ] ℂ) ℂ (WeightOne.CM.Complexification E) :=
  Module.Basis.ofEquivFun (EmbeddingDecomposition.CM.fieldComplexificationEquiv E)

@[simp]
theorem EmbeddingDecomposition.CM.fieldEmbeddingBasis_apply (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.fieldEmbeddingBasis E σ = EmbeddingDecomposition.CM.embeddingVector E σ := by
  simp [EmbeddingDecomposition.CM.fieldEmbeddingBasis, EmbeddingDecomposition.CM.embeddingVector]

section ModuleAction

variable (U : Type*) [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]

/-- The simultaneous eigenspace of the actual scalar action for an embedding. -/
def EmbeddingDecomposition.CM.embeddingSpace (σ : E →ₐ[ℚ] ℂ) : Submodule ℂ (WeightOne.CM.Complexification U) :=
  ⨅ a : E, Module.End.eigenspace ((WeightOne.CM.scalarEndomorphism (U := U) E a).baseChange ℂ) (σ a)

omit [NumberField E] [IsScalarTower ℚ E U] in
@[simp]
theorem EmbeddingDecomposition.CM.mem_embeddingSpace (σ : E →ₐ[ℚ] ℂ) (x : WeightOne.CM.Complexification U) :
    x ∈ EmbeddingDecomposition.CM.embeddingSpace E U σ ↔
      ∀ a : E, (WeightOne.CM.scalarEndomorphism E a).baseChange ℂ x = σ a • x := by
  simp only [EmbeddingDecomposition.CM.embeddingSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

end ModuleAction

variable {E}
variable {U : Type*} [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (h : WeightOne.CM.RankOneCMAction E H)

/-- Complexification of the actual rank-one module, with all its embedding
coordinates. The choice of a field-linear generator only normalizes the vectors. -/
def WeightOne.CM.RankOneCMAction.complexEmbeddingEquiv : WeightOne.CM.Complexification U ≃ₗ[ℂ] ((E →ₐ[ℚ] ℂ) → ℂ) :=
  ((h.equivField.restrictScalars ℚ).baseChange ℚ ℂ _ _).trans
    (EmbeddingDecomposition.CM.fieldComplexificationEquiv E)

@[simp]
theorem WeightOne.CM.RankOneCMAction.complexEmbeddingEquiv_tmul (z : ℂ) (u : U) (σ : E →ₐ[ℚ] ℂ) :
    h.complexEmbeddingEquiv (z ⊗ₜ[ℚ] u) σ = z * σ (h.equivField u) := by
  simp [WeightOne.CM.RankOneCMAction.complexEmbeddingEquiv]

/-- Scalar multiplication on the rank-one module is diagonal in its
embedding coordinates. -/
theorem WeightOne.CM.RankOneCMAction.complexEmbeddingEquiv_scalar (a : E) (x : WeightOne.CM.Complexification U)
    (σ : E →ₐ[ℚ] ℂ) :
    h.complexEmbeddingEquiv ((WeightOne.CM.scalarEndomorphism E a).baseChange ℂ x) σ =
      σ a * h.complexEmbeddingEquiv x σ := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, mul_add]
  | tmul z u => simp [WeightOne.CM.scalarEndomorphism, mul_left_comm]

/-- A basis of the complexified rank-one module indexed by field embeddings. -/
def WeightOne.CM.RankOneCMAction.embeddingBasis : Module.Basis (E →ₐ[ℚ] ℂ) ℂ (WeightOne.CM.Complexification U) :=
  Module.Basis.ofEquivFun h.complexEmbeddingEquiv

@[simp]
theorem WeightOne.CM.RankOneCMAction.complexEmbeddingEquiv_embeddingBasis (σ : E →ₐ[ℚ] ℂ) :
    h.complexEmbeddingEquiv (h.embeddingBasis σ) = Pi.single σ 1 := by
  simp [WeightOne.CM.RankOneCMAction.embeddingBasis]

/-- Every embedding basis vector has the specified eigenvalue for every
field scalar. -/
theorem WeightOne.CM.RankOneCMAction.embeddingBasis_eigen (a : E) (σ : E →ₐ[ℚ] ℂ) :
    (WeightOne.CM.scalarEndomorphism E a).baseChange ℂ (h.embeddingBasis σ) =
      σ a • h.embeddingBasis σ := by
  apply h.complexEmbeddingEquiv.injective
  ext τ
  rw [h.complexEmbeddingEquiv_scalar, map_smul, h.complexEmbeddingEquiv_embeddingBasis]
  by_cases he : σ = τ
  · subst τ
    simp
  · simp [he]

/-- An eigenvector belonging to one embedding has zero coordinates at every
other embedding. Distinct field embeddings are separated by a field element. -/
theorem WeightOne.CM.RankOneCMAction.embeddingSpace_coordinate_zero (σ τ : E →ₐ[ℚ] ℂ) (hne : τ ≠ σ)
    {x : WeightOne.CM.Complexification U} (hx : x ∈ EmbeddingDecomposition.CM.embeddingSpace E U σ) :
    h.complexEmbeddingEquiv x τ = 0 := by
  have ha : ∃ a : E, τ a ≠ σ a := by
    by_contra hnot
    push Not at hnot
    exact hne (AlgHom.ext hnot)
  obtain ⟨a, ha⟩ := ha
  have he := congrArg (fun y => h.complexEmbeddingEquiv y τ)
    ((EmbeddingDecomposition.CM.mem_embeddingSpace E U σ x).mp hx a)
  rw [h.complexEmbeddingEquiv_scalar, map_smul] at he
  change τ a * h.complexEmbeddingEquiv x τ = σ a * h.complexEmbeddingEquiv x τ at he
  by_contra hz
  exact ha (mul_right_cancel₀ hz he)

/-- Each simultaneous eigenspace is exactly the line of its embedding
basis vector. This excludes extra vectors with the same eigencharacter. -/
theorem WeightOne.CM.RankOneCMAction.embeddingSpace_eq_span (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.embeddingSpace E U σ = ℂ ∙ h.embeddingBasis σ := by
  apply le_antisymm
  · intro x hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨h.complexEmbeddingEquiv x σ, ?_⟩
    apply h.complexEmbeddingEquiv.injective
    ext τ
    rw [map_smul, h.complexEmbeddingEquiv_embeddingBasis]
    by_cases he : τ = σ
    · subst τ
      simp
    · rw [h.embeddingSpace_coordinate_zero σ τ he hx]
      simp [Ne.symm he]
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact (EmbeddingDecomposition.CM.mem_embeddingSpace E U σ _).mpr (fun a => h.embeddingBasis_eigen a σ)

include h in
/-- The joint eigenspaces in a rank-one CM module are genuinely one-dimensional. -/
theorem WeightOne.CM.RankOneCMAction.embeddingSpace_finrank (σ : E →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (EmbeddingDecomposition.CM.embeddingSpace E U σ) = 1 := by
  rw [h.embeddingSpace_eq_span]
  exact finrank_span_singleton (h.embeddingBasis.ne_zero σ)

end

end OAI.AlgebraicGeometry.ComplexMultiplication
