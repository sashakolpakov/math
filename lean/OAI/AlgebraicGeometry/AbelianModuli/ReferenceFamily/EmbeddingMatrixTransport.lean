import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Embedding Matrix Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport

noncomputable section

/-! The actual complexification of a marked rational map acts on each
embedding block by its coefficientwise embedded E-matrix. -/

open scoped TensorProduct

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]

omit [NumberField E] in
theorem embeddedMatrix_apply (m : (Fin 3 → E) →ₗ[E] (Fin 3 → E))
    (σ : E →ₐ[ℚ] ℂ) (x : Fin 3 → E) (i : Fin 3) :
    ((LinearMap.toMatrix' m).map σ).mulVec (fun j => σ (x j)) i = σ (m x i) :=
  (RingHom.map_mulVec σ.toRingHom (LinearMap.toMatrix' m) x i).symm.trans
    (congrArg σ (congrFun (LinearMap.toMatrix'_mulVec m x) i))

variable {U V : Type*} [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]
    [AddCommGroup V] [Module ℚ V] [Module E V] [IsScalarTower ℚ E V]
    (eU : U ≃ₗ[E] (Fin 3 → E)) (eV : V ≃ₗ[E] (Fin 3 → E))

theorem rankThreeComplexCoordinates_map (f : U →ₗ[ℚ] V)
    (m : (Fin 3 → E) →ₗ[E] (Fin 3 → E)) (hf : ∀ v, eV (f v) = m (eU v))
    (u : ComplexMultiplication.WeightOne.CM.Complexification U) (σ : E →ₐ[ℚ] ℂ) :
    RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E eV (f.baseChange ℂ u) σ =
      ((LinearMap.toMatrix' m).map σ).mulVec (RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E eU u σ) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [map_add, Pi.add_apply, Matrix.mulVec_add, hu, hv]
  | tmul z v =>
    have hU : RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E eU (z ⊗ₜ[ℚ] v) σ = z • (fun i => σ (eU v i)) := by
      funext i
      exact RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates_tmul E eU z v σ i
    rw [LinearMap.baseChange_tmul, hU, Matrix.mulVec_smul]
    funext i
    rw [RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates_tmul, hf]
    change z * σ (m (eU v) i) = z * (((LinearMap.toMatrix' m).map σ).mulVec (fun j => σ (eU v j)) i)
    rw [embeddedMatrix_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingMatrixTransport
