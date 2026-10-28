import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixReflectionEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.ReflectionCoefficients

/-! # Reflection Congruence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.ReflectionCongruence

noncomputable section

/-! The actual reflection-product matrices are congruent to the identity
over a local coefficient subring. Every coefficient of their differences
is constructed as a level multiple in that subring, in both product orders.
-/

variable {K : Type*} [Field K]

theorem matrixReflectionForm_mem_subring
    (S : Subring K) (σ : K →+* K) (H : Matrix (Fin 3) (Fin 3) K)
    (hH : ∀ i j, H i j ∈ S) (x y : Fin 3 → K)
    (hx : ∀ i, x i ∈ S) (hy : ∀ i, σ (y i) ∈ S) :
    MatrixReflectionEmbedding.matrixReflectionForm σ H x y ∈ S := by
  rw [MatrixReflectionEmbedding.matrixReflectionForm_apply]
  apply S.sum_mem
  intro i _
  apply S.sum_mem
  intro j _
  exact S.mul_mem (S.mul_mem (hx i) (hH i j)) (hy j)

theorem twoMatrixReflections_local_congruence
    (S : Subring K) [IsLocalRing S]
    (σ : K →+* K) (hσ : Function.Involutive σ)
    (H : Matrix (Fin 3) (Fin 3) K) (hHerm : ∀ i j, H i j = σ (H j i))
    (hH : ∀ i j, H i j ∈ S)
    (ℓ : S) (hℓ : ℓ ∈ IsLocalRing.maximalIdeal S) (hℓσ : σ (ℓ : K) = (ℓ : K))
    (w c : Fin 3 → K)
    (hwS : ∀ i, w i ∈ S) (hwσS : ∀ i, σ (w i) ∈ S)
    (hcS : ∀ i, c i ∈ S) (hcσS : ∀ i, σ (c i) ∈ S)
    (hw : MatrixReflectionEmbedding.matrixReflectionForm σ H w w ≠ 0)
    (hv : MatrixReflectionEmbedding.matrixReflectionForm σ H
      (w + ((ℓ : K) * (MatrixReflectionEmbedding.matrixReflectionForm σ H w w) ^ 2) • c)
      (w + ((ℓ : K) * (MatrixReflectionEmbedding.matrixReflectionForm σ H w w) ^ 2) • c) ≠ 0) :
    let B := MatrixReflectionEmbedding.matrixReflectionForm σ H
    let v := w + ((ℓ : K) * (B w w) ^ 2) • c
    ∀ i j : Fin 3, ∃ a b : S,
      LinearMap.toMatrix' (ReflectionDeterminant.twoHermitianReflections σ B v w hv hw).toLinearMap i j -
        (1 : Matrix (Fin 3) (Fin 3) K) i j = (ℓ : K) * (a : K) ∧
      LinearMap.toMatrix' (ReflectionDeterminant.twoHermitianReflections σ B w v hw hv).toLinearMap i j -
        (1 : Matrix (Fin 3) (Fin 3) K) i j = (ℓ : K) * (b : K) := by
  classical
  dsimp only
  let B := MatrixReflectionEmbedding.matrixReflectionForm σ H
  let q : S := ⟨B w w, matrixReflectionForm_mem_subring S σ H hH w w hwS hwσS⟩
  let s : S := ⟨B w c, matrixReflectionForm_mem_subring S σ H hH w c hwS hcσS⟩
  let t : S := ⟨B c w, matrixReflectionForm_mem_subring S σ H hH c w hcS hwσS⟩
  let r : S := ⟨B c c, matrixReflectionForm_mem_subring S σ H hH c c hcS hcσS⟩
  intro i j
  have heS : ∀ k : Fin 3, (Pi.single j (1 : K) : Fin 3 → K) k ∈ S := by
    intro k
    by_cases h : k = j <;> simp [h]
  let p : S := ⟨B (Pi.single j 1) w,
    matrixReflectionForm_mem_subring S σ H hH _ w heS hwσS⟩
  let d : S := ⟨B (Pi.single j 1) c,
    matrixReflectionForm_mem_subring S σ H hH _ c heS hcσS⟩
  let a₀ : S := ⟨w i, hwS i⟩
  let c₀ : S := ⟨c i, hcS i⟩
  let F : S := ReflectionCongruenceCoefficients.forwardReflectionDifferencePolynomial q (ℓ * q ^ 2) a₀ c₀ p d s t r
  let G : S := ReflectionCongruenceCoefficients.reverseReflectionDifferencePolynomial q (ℓ * q ^ 2) a₀ c₀ p d s t r
  obtain ⟨a, ha⟩ := ReflectionCongruenceCoefficients.local_reflection_norm_division_is_level_multiple S.subtype ℓ q s t r F hℓ
  obtain ⟨b, hb⟩ := ReflectionCongruenceCoefficients.local_reflection_norm_division_is_level_multiple S.subtype ℓ q s t r G hℓ
  refine ⟨a, b, ?_, ?_⟩
  · exact (Hermitian.ReflectionCoefficients.twoHermitianReflections_level_coefficient σ B
      (MatrixReflectionEmbedding.matrixReflectionForm_symmetry σ hσ H hHerm) (ℓ : K) hℓσ w c hw hv i j).trans ha
  · exact (Hermitian.ReflectionCoefficients.reverseTwoHermitianReflections_level_coefficient σ B
      (MatrixReflectionEmbedding.matrixReflectionForm_symmetry σ hσ H hHerm) (ℓ : K) hℓσ w c hw hv i j).trans hb

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.ReflectionCongruence
