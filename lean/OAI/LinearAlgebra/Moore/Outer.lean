import OAI.LinearAlgebra.Moore.Corank

/-! Rank-one affine dependence in arbitrary quaternionic directions. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.Calculus.Quaternion

theorem exists_right_inverse_of_mulVec_injective {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hi : Function.Injective A.mulVec) :
    ∃ C : Matrix (Fin n) (Fin n) (Quaternion ℝ), A * C = 1 := by
  have hs : Function.Surjective (quaternionMulVecLinear A) :=
    LinearMap.surjective_of_injective hi
  choose v hv using hs
  let C : Matrix (Fin n) (Fin n) (Quaternion ℝ) := fun i j ↦ v (Pi.single j 1) i
  refine ⟨C, ?_⟩
  apply Matrix.ext
  intro i j
  have h := congrFun (hv (Pi.single j 1)) i
  change (A *ᵥ v (Pi.single j 1)) i = (Pi.single j (1 : Quaternion ℝ) : Fin n → Quaternion ℝ) i at h
  change (A *ᵥ v (Pi.single j 1)) i = (1 : Matrix _ _ _) i j
  simpa only [Matrix.one_apply, Pi.single_apply, eq_comm] using h

def columnExtension {n : ℕ} (v : Fin n → Quaternion ℝ) (k : Fin n) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
  1 + vecMulVec (v - Pi.single k 1) (Pi.single k 1)

theorem columnExtension_mulVec {n : ℕ} (v x : Fin n → Quaternion ℝ) (k : Fin n) :
    columnExtension v k *ᵥ x = fun i ↦ x i +
      (v i - (Pi.single k (1 : Quaternion ℝ) : Fin n → Quaternion ℝ) i) * x k := by
  funext i
  rw [columnExtension, Matrix.add_mulVec, Matrix.one_mulVec]
  change x i + (∑ j, ((v i - (Pi.single k (1 : Quaternion ℝ) : Fin n → Quaternion ℝ) i) *
    (Pi.single k (1 : Quaternion ℝ) : Fin n → Quaternion ℝ) j) * x j) = _
  simp [Pi.single_apply, mul_ite, ite_mul]

theorem columnExtension_mulVec_injective {n : ℕ} (v : Fin n → Quaternion ℝ)
    (k : Fin n) (hk : v k ≠ 0) : Function.Injective (columnExtension v k).mulVec := by
  change Function.Injective (quaternionMulVecLinear (columnExtension v k))
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have he : columnExtension v k *ᵥ x = 0 := hx
  have hh := congrFun he k
  rw [columnExtension_mulVec] at hh
  simp only [Pi.single_eq_same, Pi.zero_apply] at hh
  have hvx : v k * x k = 0 := by
    calc
      v k * x k = x k + (v k - 1) * x k := by noncomm_ring
      _ = 0 := hh
  have hxk : x k = 0 := (mul_eq_zero.mp hvx).resolve_left hk
  funext i
  have hi := congrFun he i
  rw [columnExtension_mulVec] at hi
  simpa only [hxk, mul_zero, add_zero] using hi

theorem columnExtension_column {n : ℕ} (v : Fin n → Quaternion ℝ) (k : Fin n) :
    columnExtension v k *ᵥ Pi.single k 1 = v := by
  rw [columnExtension_mulVec]
  funext i
  simp

theorem outer_congruence {n : ℕ} (B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (v : Fin n → Quaternion ℝ) : B * OAI.Analysis.Calculus.Quaternion.outer v * Bᴴ = OAI.Analysis.Calculus.Quaternion.outer (B *ᵥ v) := by
  change B * vecMulVec v (star v) * Bᴴ = vecMulVec (B *ᵥ v) (star (B *ᵥ v))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

theorem coordinateProjector_eq_outer {n : ℕ} (k : Fin n) :
    coordinateProjector n k = OAI.Analysis.Calculus.Quaternion.outer (Pi.single k (1 : Quaternion ℝ)) := by
  apply Matrix.ext
  intro i j
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp [coordinateProjector, OAI.Analysis.Calculus.Quaternion.outer, hi, hj]

theorem columnExtension_projector {n : ℕ} (v : Fin n → Quaternion ℝ) (k : Fin n) :
    columnExtension v k * coordinateProjector n k * (columnExtension v k)ᴴ = OAI.Analysis.Calculus.Quaternion.outer v := by
  rw [coordinateProjector_eq_outer, outer_congruence, columnExtension_column]

/-- Affineness in a completely arbitrary quaternionic rank-one direction. -/
theorem mooreDet_add_outer {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v : Fin n → Quaternion ℝ) (t : ℝ) :
    mooreDet n (A + t • OAI.Analysis.Calculus.Quaternion.outer v) = mooreDet n A +
      t * (mooreDet n (A + OAI.Analysis.Calculus.Quaternion.outer v) - mooreDet n A) := by
  by_cases hv : v = 0
  · subst v
    have hz : OAI.Analysis.Calculus.Quaternion.outer (0 : Fin n → Quaternion ℝ) = 0 := by ext i j <;> simp [OAI.Analysis.Calculus.Quaternion.outer]
    simp only [hz, smul_zero, add_zero, sub_self, mul_zero]
  · obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    let B := columnExtension v k
    obtain ⟨C, hBC⟩ := exists_right_inverse_of_mulVec_injective B
      (columnExtension_mulVec_injective v k hk)
    let D := C * A * Cᴴ
    have hstar : Cᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hBC, Matrix.conjTranspose_one]
    have hbase : B * D * Bᴴ = A := by
      calc
        B * D * Bᴴ = (B * C) * A * (Cᴴ * Bᴴ) := by simp only [D, Matrix.mul_assoc]
        _ = A := by rw [hBC, hstar, Matrix.one_mul, Matrix.mul_one]
    have hproj : B * coordinateProjector n k * Bᴴ = OAI.Analysis.Calculus.Quaternion.outer v := columnExtension_projector v k
    have hrep (s : ℝ) : B * (D + s • coordinateProjector n k) * Bᴴ = A + s • OAI.Analysis.Calculus.Quaternion.outer v := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hbase, hproj]
    have hf (s : ℝ) : mooreDet n (A + s • OAI.Analysis.Calculus.Quaternion.outer v) = (complexify B).det.re *
        (mooreDet n D + s * (mooreDet n (D + coordinateProjector n k) - mooreDet n D)) := by
      rw [← hrep s, mooreDet_congruence, mooreDet_add_coordinate]
    have h0 := hf 0
    have h1 := hf 1
    simp only [zero_smul, add_zero, zero_mul] at h0
    simp only [one_smul, one_mul] at h1
    linear_combination hf t - (1 - t) * h0 - t * h1

theorem mooreDifferential_outer {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v : Fin n → Quaternion ℝ) :
    mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.outer v) = mooreDet n (A + OAI.Analysis.Calculus.Quaternion.outer v) - mooreDet n A := by
  have hc : HasDerivAt (fun s : ℝ ↦ mooreDet n (A + s • OAI.Analysis.Calculus.Quaternion.outer v))
      (mooreDet n (A + OAI.Analysis.Calculus.Quaternion.outer v) - mooreDet n A) 0 := by
    simp_rw [mooreDet_add_outer]
    convert! ((hasDerivAt_id (0 : ℝ)).mul_const
      (mooreDet n (A + OAI.Analysis.Calculus.Quaternion.outer v) - mooreDet n A)).const_add (mooreDet n A) using 1
    simp
  have hd := hasDerivAt_mooreDet_affine A (OAI.Analysis.Calculus.Quaternion.outer v) 0
  simpa only [zero_smul, add_zero] using hd.unique hc

theorem mooreDet_add_outer_differential {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v : Fin n → Quaternion ℝ) (t : ℝ) :
    mooreDet n (A + t • OAI.Analysis.Calculus.Quaternion.outer v) = mooreDet n A + t * mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.outer v) := by
  rw [mooreDet_add_outer, mooreDifferential_outer]

end OAI.LinearAlgebra.Moore
