import OAI.LinearAlgebra.Moore.Cofactor

/-! Smoothness of the signed determinant, its differential, and its cofactor,
including at singular matrices. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

theorem contDiff_skewComplexify_entry {n : ℕ} (k : ℕ∞ω) (i j : Fin n × Fin 2) :
    ContDiff ℝ k (fun A : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦ skewComplexify A i j) := by
  exact (skewQuaternionEntryCLM i.2 j.2).contDiff.comp
    (contDiff_apply_apply ℝ (Quaternion ℝ) i.1 j.1)

theorem contDiff_mooreDet (n : ℕ) (k : ℕ∞ω) : ContDiff ℝ k (mooreDet n) := by
  change ContDiff ℝ k (Complex.reCLM ∘ fun A : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦
    pfaffian n (skewComplexify A))
  apply (Complex.reCLM.contDiff : ContDiff ℝ k Complex.reCLM).comp
  unfold pfaffian
  apply contDiff_const.mul
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact contDiff_skewComplexify_entry k (σ (i, 0)) (σ (i, 1))

theorem contDiff_mooreDifferential_left (n : ℕ) (k : ℕ∞ω)
    (D : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    ContDiff ℝ k (fun A ↦ mooreDifferential n A D) := by
  change ContDiff ℝ k (Complex.reCLM ∘ fun A : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦
    pfaffianDifferential n (skewComplexify A) (skewComplexify D))
  apply (Complex.reCLM.contDiff : ContDiff ℝ k Complex.reCLM).comp
  unfold pfaffianDifferential
  apply contDiff_const.mul
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply ContDiff.sum
  intro i _
  apply ContDiff.mul _ contDiff_const
  apply contDiff_prod
  intro j _
  exact contDiff_skewComplexify_entry k (σ (j, 0)) (σ (j, 1))

theorem quaternionDualVector_eq (L : Quaternion ℝ →ₗ[ℝ] ℝ) :
    quaternionDualVector L = L 1 • (1 : Quaternion ℝ) +
      L ⟨0, 1, 0, 0⟩ • (⟨0, 1, 0, 0⟩ : Quaternion ℝ) +
      L ⟨0, 0, 1, 0⟩ • (⟨0, 0, 1, 0⟩ : Quaternion ℝ) +
      L ⟨0, 0, 0, 1⟩ • (⟨0, 0, 0, 1⟩ : Quaternion ℝ) := by
  ext <;> simp [quaternionDualVector]

theorem contDiff_rawCofactor (n : ℕ) (k : ℕ∞ω) : ContDiff ℝ k (rawCofactor n) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [rawCofactor, quaternionDualVector_eq]
  apply quaternionStarCLM.contDiff.comp
  change ContDiff ℝ k (fun A ↦
    mooreDifferential n A (single j i 1) • (1 : Quaternion ℝ) +
      mooreDifferential n A (single j i ⟨0, 1, 0, 0⟩) • (⟨0, 1, 0, 0⟩ : Quaternion ℝ) +
      mooreDifferential n A (single j i ⟨0, 0, 1, 0⟩) • (⟨0, 0, 1, 0⟩ : Quaternion ℝ) +
      mooreDifferential n A (single j i ⟨0, 0, 0, 1⟩) • (⟨0, 0, 0, 1⟩ : Quaternion ℝ))
  exact (((contDiff_mooreDifferential_left n k _).smul contDiff_const).add
    ((contDiff_mooreDifferential_left n k _).smul contDiff_const) |>.add
    ((contDiff_mooreDifferential_left n k _).smul contDiff_const)).add
    ((contDiff_mooreDifferential_left n k _).smul contDiff_const)

theorem contDiff_mooreCofactor (n : ℕ) (k : ℕ∞ω) : ContDiff ℝ k (mooreCofactor n) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ k (fun A ↦ (1 / 2 : ℝ) •
    (rawCofactor n A i j + star (rawCofactor n A j i)))
  have h₁ := (contDiff_pi.mp (contDiff_pi.mp (contDiff_rawCofactor n k) i)) j
  have h₂ := quaternionStarCLM.contDiff.comp
    ((contDiff_pi.mp (contDiff_pi.mp (contDiff_rawCofactor n k) j)) i)
  exact (contDiff_const : ContDiff ℝ k (fun _ : Matrix (Fin n) (Fin n) (Quaternion ℝ) ↦
    (1 / 2 : ℝ))).smul (h₁.add h₂)

end OAI.LinearAlgebra.Moore
