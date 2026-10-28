import OAI.Analysis.PDE.Dirichlet.NormalEntry
import OAI.LinearAlgebra.Moore.Boundary

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem normal_basis_pairing {n : ℕ} (ν : Fin (n + 1) → Q)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) Q)
    (hν : quaternionPairing ν ν = 1) (hcol : (fun i ↦ B i 0) = ν)
    (ht : ∀ j : Fin n, quaternionPairing ν (fun i ↦ B i j.succ) = 0)
    (z : Fin (n + 1) → Q) : quaternionPairing ν (B *ᵥ z) = z 0 := by
  rw [quaternionPairing_mulVec, Fin.sum_univ_succ, hcol, hν]
  simp only [ht, zero_mul, Finset.sum_const_zero, add_zero, one_mul]

theorem normal_basis_dual {n : ℕ} (ν : Fin (n + 1) → Q)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) Q)
    (hν : quaternionPairing ν ν = 1) (hcol : (fun i ↦ B i 0) = ν)
    (ht : ∀ j : Fin n, quaternionPairing ν (fun i ↦ B i j.succ) = 0) :
    Bᴴ *ᵥ ν = Pi.single 0 1 := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change quaternionPairing (fun i ↦ B i 0) ν = _
    rw [hcol, hν]
    simp
  · change quaternionPairing (fun i ↦ B i j.succ) ν = _
    rw [← star_quaternionPairing, ht, star_zero]
    simp [Fin.succ_ne_zero]

theorem complexify_det_adjoint_nonneg {n : ℕ} (B : Matrix (Fin n) (Fin n) Q) :
    0 ≤ (OAI.LinearAlgebra.Moore.complexify Bᴴ).det.re := by
  rw [← OAI.LinearAlgebra.Moore.mooreDet_gram]
  apply OAI.LinearAlgebra.Moore.mooreDet_nonneg_of_complexify_posSemidef
  simp only [Matrix.conjTranspose_conjTranspose, OAI.LinearAlgebra.Moore.complexify_mul, OAI.LinearAlgebra.Moore.complexify_star]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The determinant's coefficient in the normal rank-one direction is
strictly positive whenever its tangential restriction is positive. This
does not assume positivity of the full matrix. -/
theorem moore_normal_coefficient_pos {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) Q) (hA : A.IsHermitian)
    (ν : Fin (n + 1) → Q) (hν : quaternionPairing ν ν = 1)
    (hT : ∀ z : Fin (n + 1) → Q, z ≠ 0 → quaternionPairing ν z = 0 →
      0 < (quaternionForm A z).re) :
    0 < OAI.LinearAlgebra.Moore.mooreDifferential (n + 1) A (OAI.Analysis.Calculus.Quaternion.outer ν) := by
  obtain ⟨B, hcol, hBi, ht⟩ := exists_normal_tangent_basis ν hν
  have hH : (Bᴴ * A * B).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul B hA
  have hTB : ∀ z : Fin (n + 1) → Q, z ≠ 0 → z 0 = 0 →
      0 < (quaternionForm (Bᴴ * A * B) z).re := by
    intro z hz hz0
    rw [quaternionForm_congruence]
    apply hT _ ?_ ((normal_basis_pairing ν B hν hcol ht z).trans hz0)
    intro he
    apply hz
    apply hBi
    simpa using he
  have hpos := normal_cofactor_pos_of_tangent (Bᴴ * A * B) hH hTB
  have hout : Bᴴ * OAI.Analysis.Calculus.Quaternion.outer ν * B = OAI.LinearAlgebra.Moore.coordinateProjector (n + 1) 0 := by
    have ho := OAI.LinearAlgebra.Moore.outer_congruence Bᴴ ν
    simpa only [Matrix.conjTranspose_conjTranspose,
      normal_basis_dual ν B hν hcol ht, OAI.LinearAlgebra.Moore.coordinateProjector_eq_outer] using ho
  have hsum : Bᴴ * (A + OAI.Analysis.Calculus.Quaternion.outer ν) * B = Bᴴ * A * B + OAI.LinearAlgebra.Moore.coordinateProjector (n + 1) 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, hout]
  have hdet (D : Matrix (Fin (n + 1)) (Fin (n + 1)) Q) :
      OAI.LinearAlgebra.Moore.mooreDet (n + 1) (Bᴴ * D * B) = (OAI.LinearAlgebra.Moore.complexify Bᴴ).det.re * OAI.LinearAlgebra.Moore.mooreDet (n + 1) D := by
    simpa only [Matrix.conjTranspose_conjTranspose] using OAI.LinearAlgebra.Moore.mooreDet_congruence (n + 1) D Bᴴ
  rw [OAI.LinearAlgebra.Moore.mooreCofactor_diag, ← hsum, hdet, hdet] at hpos
  rw [OAI.LinearAlgebra.Moore.mooreDifferential_outer]
  have hnonneg := complexify_det_adjoint_nonneg B
  by_contra h
  have hdiff : OAI.LinearAlgebra.Moore.mooreDet (n + 1) (A + OAI.Analysis.Calculus.Quaternion.outer ν) - OAI.LinearAlgebra.Moore.mooreDet (n + 1) A ≤ 0 := le_of_not_gt h
  have hm := mul_nonpos_of_nonneg_of_nonpos hnonneg hdiff
  nlinarith

end OAI.Analysis.PDE.Dirichlet
