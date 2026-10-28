import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Rank Three Embedding Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates

noncomputable section

section

/-! The actual complexification of an E-module marked by E cubed splits
into one three-dimensional coordinate block for every embedding. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM
open scoped TensorProduct

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]

def embeddingCoordinateFlip : ((Fin 3) → (E →ₐ[ℚ] ℂ) → ℂ) ≃ₗ[ℂ] ((E →ₐ[ℚ] ℂ) → Fin 3 → ℂ) where
  toFun f σ i := f i σ
  invFun f i σ := f σ i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def standardRankThreeComplexCoordinates :
    ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E) ≃ₗ[ℂ] ((E →ₐ[ℚ] ℂ) → Fin 3 → ℂ) :=
  (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin 3 => E)).trans
    ((LinearEquiv.piCongrRight (fun _ : Fin 3 => ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E)).trans
      (embeddingCoordinateFlip E))

theorem standardRankThreeComplexCoordinates_tmul (z : ℂ) (x : Fin 3 → E)
    (σ : E →ₐ[ℚ] ℂ) (i : Fin 3) :
    standardRankThreeComplexCoordinates E (z ⊗ₜ[ℚ] x) σ i = z * σ (x i) := by
  simp [standardRankThreeComplexCoordinates, embeddingCoordinateFlip, TensorProduct.piRightHom_tmul]

variable {U : Type*} [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]

def rankThreeComplexCoordinates (e : U ≃ₗ[E] (Fin 3 → E)) :
    ComplexMultiplication.WeightOne.CM.Complexification U ≃ₗ[ℂ] ((E →ₐ[ℚ] ℂ) → Fin 3 → ℂ) :=
  ((e.restrictScalars ℚ).baseChange ℚ ℂ U (Fin 3 → E)).trans (standardRankThreeComplexCoordinates E)

theorem rankThreeComplexCoordinates_tmul (e : U ≃ₗ[E] (Fin 3 → E))
    (z : ℂ) (u : U) (σ : E →ₐ[ℚ] ℂ) (i : Fin 3) :
    rankThreeComplexCoordinates E e (z ⊗ₜ[ℚ] u) σ i = z * σ (e u i) :=
  standardRankThreeComplexCoordinates_tmul E z (e u) σ i

theorem rankThreeComplexCoordinates_scalar (e : U ≃ₗ[E] (Fin 3 → E))
    (a : E) (u : ComplexMultiplication.WeightOne.CM.Complexification U) (σ : E →ₐ[ℚ] ℂ) (i : Fin 3) :
    rankThreeComplexCoordinates E e ((ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a).baseChange ℂ u) σ i =
      σ a * rankThreeComplexCoordinates E e u σ i := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv, mul_add]
  | tmul z u =>
      rw [LinearMap.baseChange_tmul, rankThreeComplexCoordinates_tmul, rankThreeComplexCoordinates_tmul]
      change z * σ (e (a • u) i) = _
      rw [e.map_smul]
      change z * σ (a * e u i) = _
      rw [map_mul]
      ring

end

/-! Each simultaneous embedding eigenspace in the complexification of
an actual rank-three E-module is exactly its three-coordinate block. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM
open scoped TensorProduct

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    {U : Type*} [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]
    (e : U ≃ₗ[E] (Fin 3 → E))

theorem rankThreeEmbedding_coordinate_zero (σ τ : E →ₐ[ℚ] ℂ) (hne : τ ≠ σ)
    {u : ComplexMultiplication.WeightOne.CM.Complexification U} (hu : u ∈ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ) (i : Fin 3) :
    rankThreeComplexCoordinates E e u τ i = 0 := by
  have ha : ∃ a : E, τ a ≠ σ a := by
    by_contra hn
    push Not at hn
    exact hne (AlgHom.ext hn)
  obtain ⟨a, ha⟩ := ha
  have h := congrArg (fun x => rankThreeComplexCoordinates E e x τ i)
    ((ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E U σ u).mp hu a)
  have hs : τ a * rankThreeComplexCoordinates E e u τ i =
      σ a * rankThreeComplexCoordinates E e u τ i := by
    simpa only [rankThreeComplexCoordinates_scalar, map_smul, Pi.smul_apply, smul_eq_mul] using h
  by_contra hz
  exact ha (mul_right_cancel₀ hz hs)

theorem rankThreeEmbedding_mem_iff (σ : E →ₐ[ℚ] ℂ) (u : ComplexMultiplication.WeightOne.CM.Complexification U) :
    u ∈ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ ↔ ∀ τ, τ ≠ σ → rankThreeComplexCoordinates E e u τ = 0 := by
  constructor
  · intro hu τ hτ
    funext i
    exact rankThreeEmbedding_coordinate_zero E e σ τ hτ hu i
  · intro hu
    apply (ComplexMultiplication.EmbeddingDecomposition.CM.mem_embeddingSpace E U σ u).mpr
    intro a
    apply (rankThreeComplexCoordinates E e).injective
    funext τ i
    rw [rankThreeComplexCoordinates_scalar, map_smul]
    change τ a * rankThreeComplexCoordinates E e u τ i = σ a * rankThreeComplexCoordinates E e u τ i
    by_cases hτ : τ = σ
    · rw [hτ]
    · have hz := congrFun (hu τ hτ) i
      rw [hz, Pi.zero_apply, mul_zero, mul_zero]

def rankThreeEmbeddingSpaceEquiv (σ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ ≃ₗ[ℂ] (Fin 3 → ℂ) := by
  classical
  exact
    { toFun := fun u => rankThreeComplexCoordinates E e u.val σ
      invFun := fun v => ⟨(rankThreeComplexCoordinates E e).symm (Pi.single σ v), by
        apply (rankThreeEmbedding_mem_iff E e σ _).mpr
        intro τ hτ
        rw [LinearEquiv.apply_symm_apply]
        exact Pi.single_eq_of_ne (M := fun _ : E →ₐ[ℚ] ℂ => Fin 3 → ℂ) hτ v⟩
      left_inv := by
        intro u
        apply Subtype.ext
        apply (rankThreeComplexCoordinates E e).injective
        rw [LinearEquiv.apply_symm_apply]
        funext τ
        by_cases hτ : τ = σ
        · subst τ
          simp only [Pi.single_eq_same]
        · have hs : Pi.single (M := fun _ : E →ₐ[ℚ] ℂ => Fin 3 → ℂ)
              σ (rankThreeComplexCoordinates E e u.val σ) τ = (0 : Fin 3 → ℂ) :=
            Pi.single_eq_of_ne (M := fun _ : E →ₐ[ℚ] ℂ => Fin 3 → ℂ) hτ
              (rankThreeComplexCoordinates E e u.val σ)
          exact hs.trans ((rankThreeEmbedding_mem_iff E e σ u.val).mp u.property τ hτ).symm
      right_inv := by
        intro v
        change rankThreeComplexCoordinates E e ((rankThreeComplexCoordinates E e).symm (Pi.single σ v)) σ = v
        rw [LinearEquiv.apply_symm_apply]
        simp only [Pi.single_eq_same]
      map_add' := fun u v => congrFun ((rankThreeComplexCoordinates E e).map_add u.val v.val) σ
      map_smul' := fun z u => congrFun ((rankThreeComplexCoordinates E e).map_smul z u.val) σ }

include e in
theorem rankThreeEmbeddingSpace_finrank (σ : E →ₐ[ℚ] ℂ) :
    Module.finrank ℂ (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ) = 3 :=
  (rankThreeEmbeddingSpaceEquiv E e σ).finrank_eq.trans (Module.finrank_fin_fun ℂ)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates
