import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar Descent -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM

noncomputable section

/-!
# Scalar traces for the CM tensor reduction

This supplies the finite-coefficient descent used in Section 2 of the
manuscript. Conjugation here changes scalar coefficients in a tensor
product; it does not change an underlying complex variety.
-/

open scoped TensorProduct

variable (K L U : Type*) [Field K] [Field L] [Algebra K L]
  [AddCommGroup U] [Module K U]

/-- Apply the field trace to the coefficient factor. -/
def scalarTrace : L ⊗[K] U →ₗ[K] U :=
  (TensorProduct.lid K U).toLinearMap.comp
    (TensorProduct.map (Algebra.trace K L) LinearMap.id)

@[simp]
theorem scalarTrace_tmul (a : L) (u : U) :
    scalarTrace K L U (a ⊗ₜ[K] u) = Algebra.trace K L a • u := rfl

/-- An automorphism acts on scalar coefficients and fixes the rational factor. -/
def scalarConjugate (σ : L ≃ₐ[K] L) : L ⊗[K] U →ₗ[K] L ⊗[K] U :=
  TensorProduct.map σ.toLinearMap LinearMap.id

@[simp]
theorem scalarConjugate_tmul (σ : L ≃ₐ[K] L) (a : L) (u : U) :
    scalarConjugate K L U σ (a ⊗ₜ[K] u) = σ a ⊗ₜ[K] u := rfl

theorem scalarConjugate_smul (σ : L ≃ₐ[K] L) (a : L) (x : L ⊗[K] U) :
    scalarConjugate K L U σ (a • x) = σ a • scalarConjugate K L U σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul b u => simp [TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

section Separable

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K L)

theorem traceDual_coordinate (a : L) (i : ι) :
    b.repr a i = Algebra.trace K L (b.traceDual i * a) := by
  simpa [Algebra.traceForm_apply, mul_comm] using b.traceDual.traceDual_repr_apply a i

/-- Traces against a dual basis recover every coefficient tensor. -/
theorem scalarTrace_reconstruction (x : L ⊗[K] U) :
    ∑ i, b i ⊗ₜ[K] scalarTrace K L U (b.traceDual i • x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a u =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, scalarTrace_tmul]
    calc
      ∑ i, b i ⊗ₜ[K] (Algebra.trace K L (b.traceDual i * a) • u) =
          (∑ i, b.repr a i • b i) ⊗ₜ[K] u := by
        rw [TensorProduct.sum_tmul]
        apply Finset.sum_congr rfl
        intro i _
        rw [traceDual_coordinate K L b a i, TensorProduct.smul_tmul]
      _ = a ⊗ₜ[K] u := by rw [b.sum_repr]
  | add x y hx hy =>
    simp only [smul_add, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

end Separable

variable [FiniteDimensional K L] [IsGalois K L]

/-- The trace tensor is the actual sum of scalar Galois conjugates. -/
theorem scalarTrace_eq_sum_conjugates (x : L ⊗[K] U) :
    (1 : L) ⊗ₜ[K] scalarTrace K L U x =
      ∑ σ : L ≃ₐ[K] L, scalarConjugate K L U σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a u =>
    simp only [scalarTrace_tmul, scalarConjugate_tmul]
    rw [← TensorProduct.sum_tmul, ← trace_eq_sum_automorphisms]
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

/-- Traces of scalar multiples lie in a subspace containing the entire scalar orbit. -/
theorem scalarTrace_mem_of_conjugates (P : Submodule L (L ⊗[K] U))
    {x : L ⊗[K] U} (hx : ∀ σ, scalarConjugate K L U σ x ∈ P) (a : L) :
    (1 : L) ⊗ₜ[K] scalarTrace K L U (a • x) ∈ P := by
  rw [scalarTrace_eq_sum_conjugates]
  apply P.sum_mem
  intro σ _
  rw [scalarConjugate_smul]
  exact P.smul_mem (σ a) (hx σ)

/-- If every scalar conjugate of a tensor lies in a subspace, that tensor is
in the scalar span of the vectors in the subspace defined over the base field.
This is the scalar-descent assertion used for Hodge tensors and Hodge maps. -/
theorem mem_span_baseField_of_conjugates (P : Submodule L (L ⊗[K] U))
    {x : L ⊗[K] U} (hx : ∀ σ, scalarConjugate K L U σ x ∈ P) :
    x ∈ Submodule.span L {y | ∃ u : U, y = (1 : L) ⊗ₜ[K] u ∧ y ∈ P} := by
  classical
  let b := Module.finBasis K L
  rw [← scalarTrace_reconstruction K L U b x]
  apply Submodule.sum_mem
  intro i _
  have hmem : (1 : L) ⊗ₜ[K] scalarTrace K L U (b.traceDual i • x) ∈
      Submodule.span L {y | ∃ u : U, y = (1 : L) ⊗ₜ[K] u ∧ y ∈ P} :=
    Submodule.subset_span ⟨_, rfl, scalarTrace_mem_of_conjugates K L U P hx _⟩
  simpa [TensorProduct.smul_tmul', smul_eq_mul] using
    Submodule.smul_mem _ (b i) hmem

/-- A subspace stable under scalar Galois conjugation descends to the base field. -/
theorem galoisStable_submodule_eq_span_baseField (P : Submodule L (L ⊗[K] U))
    (hP : ∀ σ x, x ∈ P → scalarConjugate K L U σ x ∈ P) :
    P = Submodule.span L {y | ∃ u : U, y = (1 : L) ⊗ₜ[K] u ∧ y ∈ P} := by
  apply le_antisymm
  · intro x hx
    exact mem_span_baseField_of_conjugates K L U P (fun σ => hP σ x hx)
  · apply Submodule.span_le.mpr
    rintro x ⟨_, _, hx⟩
    exact hx

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM
