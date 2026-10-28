import OAI.Analysis.PDE.Dirichlet.Moore.Matrix

open Set InnerProductSpace
open scoped Matrix Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- Polarization identifies the entire variational pairing, not only its
quadratic symbol, with the actual real derivative operator. -/
theorem mooreRealMatrix_bilinear {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (v w : CoordinateSpace n 4) :
    (v : Fin n × Fin 4 → ℝ) ⬝ᵥ (mooreRealMatrix A *ᵥ (w : Fin n × Fin 4 → ℝ)) =
      inner ℝ v (detRealOperator A w) := by
  have hv := mooreRealMatrix_dotProduct A v
  have hw := mooreRealMatrix_dotProduct A w
  have hs := mooreRealMatrix_dotProduct A (v + w)
  simp only [star_trivial] at hv hw hs
  change ((v : Fin n × Fin 4 → ℝ) + (w : Fin n × Fin 4 → ℝ)) ⬝ᵥ
    (mooreRealMatrix A *ᵥ ((v : Fin n × Fin 4 → ℝ) + (w : Fin n × Fin 4 → ℝ))) =
      inner ℝ (v + w) (detRealOperator A (v + w)) at hs
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, map_add,
    inner_add_left, inner_add_right] at hs
  have hm := (mooreRealMatrix_isSymm A).dotProduct_mulVec_comm
    (x := (v : Fin n × Fin 4 → ℝ)) (y := (w : Fin n × Fin 4 → ℝ))
  have ht : inner ℝ w (detRealOperator A v) = inner ℝ v (detRealOperator A w) := by
    calc
      inner ℝ w (detRealOperator A v) = inner ℝ (detRealOperator A v) w :=
        real_inner_comm _ _
      _ = _ := detRealOperator_isSymmetric A v w
  linarith

theorem mooreRealMatrix_bilinear_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (v w : CoordinateSpace n 4) :
    (∑ p, ∑ q, mooreRealMatrix A p q * v p * w q) =
      inner ℝ v (detRealOperator A w) := by
  rw [← mooreRealMatrix_bilinear]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Entrywise equality connects the Banach-space derivative coefficients to
the symmetric divergence-form matrix used by the weak Dirichlet solver. -/
theorem operatorCoordinateMatrix_detRealOperator {n : ℕ}
    (A : Matrix (Fin n) (Fin n) Q) :
    operatorCoordinateMatrix (detRealOperator A) = mooreRealMatrix A := by
  apply Matrix.ext
  intro p q
  have h := mooreRealMatrix_bilinear A (coordinateVector q) (coordinateVector p)
  have he : (coordinateVector q : Fin n × Fin 4 → ℝ) ⬝ᵥ
      (mooreRealMatrix A *ᵥ (coordinateVector p : Fin n × Fin 4 → ℝ)) =
        mooreRealMatrix A q p := by
    simp [dotProduct, Matrix.mulVec, coordinateVector, PiLp.single_apply]
  rw [he] at h
  change inner ℝ (detRealOperator A (coordinateVector p)) (coordinateVector q) = _
  rw [real_inner_comm, ← h]
  exact congrFun (congrFun (mooreRealMatrix_isSymm A) p) q

end OAI.Analysis.PDE.Dirichlet
