import OAI.Analysis.PDE.Dirichlet.AffineField

open scoped Matrix

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

def realMatrixAction {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) B

/-- The real matrix of left quaternionic multiplication, in four real slots. -/
def realRepresentation {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ :=
  fun i j ↦ (star (OAI.Analysis.Calculus.Quaternion.fourSlots i.2) * A i.1 j.1 * OAI.Analysis.Calculus.Quaternion.fourSlots j.2).re

def slotMatrix (n s : ℕ) (e : Fin s → Q) : Matrix (Fin n) (Fin n × Fin s) Q :=
  fun a j ↦ if a = j.1 then e j.2 else 0

def realLift {ι κ : Type*} (H : Matrix ι κ ℝ) : Matrix ι κ Q :=
  H.map (algebraMap ℝ Q)

theorem realLift_apply {ι κ : Type*} (H : Matrix ι κ ℝ) (i : ι) (j : κ) :
    realLift H i j = H i j • (1 : Q) := by
  simp only [realLift, Matrix.map_apply, Algebra.algebraMap_eq_smul_one]

theorem realLift_mul {ι κ η : Type*} [Fintype κ]
    (H : Matrix ι κ ℝ) (B : Matrix κ η ℝ) : realLift (H * B) = realLift H * realLift B := by
  apply Matrix.ext
  intro i j
  simp only [realLift, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

theorem slotMatrix_mul_apply {n s : ℕ} {ι : Type*} (e : Fin s → Q)
    (B : Matrix (Fin n × Fin s) ι Q) (a : Fin n) (j : ι) :
    (slotMatrix n s e * B) a j = ∑ α, e α * B (a, α) j := by
  classical
  simp [slotMatrix, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul]

theorem mul_starSlot_apply {n s : ℕ} {ι : Type*} (e : Fin s → Q)
    (B : Matrix ι (Fin n × Fin s) Q) (i : ι) (a : Fin n) :
    (B * (slotMatrix n s e)ᴴ) i a = ∑ α, B i (a, α) * star (e α) := by
  classical
  simp [slotMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, apply_ite]

theorem fourSlots_right_reconstruction (q : Q) (α : Fin 4) :
    (∑ β, (star (OAI.Analysis.Calculus.Quaternion.fourSlots α) * q * OAI.Analysis.Calculus.Quaternion.fourSlots β).re • star (OAI.Analysis.Calculus.Quaternion.fourSlots β)) =
      star (OAI.Analysis.Calculus.Quaternion.fourSlots α) * q := by
  fin_cases α <;> ext <;> simp [OAI.Analysis.Calculus.Quaternion.fourSlots, Fin.sum_univ_four]

/-- The quaternionic Hessian map is compression of the real Hessian by the
slot matrix. This also fixes the multiplication order in covariance. -/
theorem hessianMap_eq_slotMatrix {n s : ℕ} (e : Fin s → Q)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) :
    OAI.Analysis.Calculus.Quaternion.hessianMap e H = slotMatrix n s e * realLift H * (slotMatrix n s e)ᴴ := by
  classical
  apply Matrix.ext
  intro a b
  rw [mul_starSlot_apply]
  simp_rw [slotMatrix_mul_apply, realLift_apply, mul_smul_comm, mul_one,
    Finset.sum_mul, smul_mul_assoc]
  unfold OAI.Analysis.Calculus.Quaternion.hessianMap
  rw [Finset.sum_comm]

theorem realRepresentation_mul_starSlot {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    realLift (realRepresentation A) * (slotMatrix n 4 OAI.Analysis.Calculus.Quaternion.fourSlots)ᴴ =
      (slotMatrix n 4 OAI.Analysis.Calculus.Quaternion.fourSlots)ᴴ * A := by
  classical
  apply Matrix.ext
  rintro ⟨a, α⟩ b
  rw [mul_starSlot_apply]
  have hr : ((slotMatrix n 4 OAI.Analysis.Calculus.Quaternion.fourSlots)ᴴ * A) (a, α) b = star (OAI.Analysis.Calculus.Quaternion.fourSlots α) * A a b := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, slotMatrix, apply_ite, ite_mul]
  rw [hr]
  simp_rw [realLift_apply, smul_mul_assoc, one_mul]
  exact fourSlots_right_reconstruction (A a b) α

theorem hessianMap_mul_realRepresentation {n : ℕ}
    (H : Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ)
    (A : Matrix (Fin n) (Fin n) Q) :
    OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (H * realRepresentation A) = OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots H * A := by
  rw [hessianMap_eq_slotMatrix, hessianMap_eq_slotMatrix]
  rw [realLift_mul, Matrix.mul_assoc, Matrix.mul_assoc, realRepresentation_mul_starSlot]
  simp only [Matrix.mul_assoc]

theorem realLift_transpose {ι κ : Type*} (H : Matrix ι κ ℝ) :
    realLift Hᵀ = (realLift H)ᴴ := by
  apply Matrix.ext
  intro i j
  simp [realLift, Matrix.conjTranspose_apply]

theorem hessianMap_transpose {n s : ℕ} (e : Fin s → Q)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) :
    OAI.Analysis.Calculus.Quaternion.hessianMap e Hᵀ = (OAI.Analysis.Calculus.Quaternion.hessianMap e H)ᴴ := by
  rw [hessianMap_eq_slotMatrix, hessianMap_eq_slotMatrix]
  simp only [realLift_transpose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

theorem hessian_toEuclideanCLM_right {n s : ℕ} (f : CoordinateSpace n s → ℝ)
    (B : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) (x : CoordinateSpace n s)
    (i j : Fin n × Fin s) :
    (fderiv ℝ (fderiv ℝ f) x (coordinateVector i))
      (realMatrixAction B (coordinateVector j)) = (realHessian f x * B) i j := by
  classical
  have hB (k : Fin n × Fin s) : (realMatrixAction B (coordinateVector j)) k = B k j := by
    simp [realMatrixAction, coordinateVector, Matrix.mulVec, dotProduct]
  rw [← realHessian_bilinear]
  simp_rw [hB]
  simp [coordinateVector, Matrix.mul_apply]

/-- Actual Hessian covariance differentiated along a real affine field, before
using that the linear part is quaternionic. -/
theorem realHessian_affineDerivative {n s : ℕ} {f : CoordinateSpace n s → ℝ}
    (hf : ContDiff ℝ 3 f) (e x : CoordinateSpace n s)
    (B : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) :
    realHessian (affineDerivative f e (realMatrixAction B)) x =
      realHessian (directionalDerivative f (e + realMatrixAction B x)) x +
        realHessian f x * B + (realHessian f x * B)ᵀ := by
  apply Matrix.ext
  intro i j
  change (fderiv ℝ (fderiv ℝ (affineDerivative f e (realMatrixAction B))) x
      (coordinateVector i)) (coordinateVector j) =
    (fderiv ℝ (fderiv ℝ (directionalDerivative f (e + realMatrixAction B x))) x
      (coordinateVector i)) (coordinateVector j) +
        (realHessian f x * B) i j + (realHessian f x * B) j i
  rw [hessian_affineDerivative hf, hessian_directionalDerivative hf,
    hessian_toEuclideanCLM_right, hessian_toEuclideanCLM_right]

/-- The actual quaternionic Hessian commutator of an affine quaternionic
vector field, with no invertibility or positivity assumption. -/
theorem quaternionHessian_affineDerivative {n : ℕ} {f : CoordinateSpace n 4 → ℝ}
    (hf : ContDiff ℝ 3 f) (e x : CoordinateSpace n 4)
    (A : Matrix (Fin n) (Fin n) Q) :
    quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (affineDerivative f e (realMatrixAction (realRepresentation A))) x =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots
        (directionalDerivative f (e + realMatrixAction (realRepresentation A) x)) x +
          quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x * A + Aᴴ * quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x := by
  unfold quaternionHessian
  rw [realHessian_affineDerivative hf, OAI.Analysis.Calculus.Quaternion.hessianMap_add, OAI.Analysis.Calculus.Quaternion.hessianMap_add,
    hessianMap_transpose]
  simp_rw [hessianMap_mul_realRepresentation]
  rw [Matrix.conjTranspose_mul]
  rw [OAI.Analysis.Calculus.Quaternion.hessianMap_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots _ (realHessian_isSymm (hf.of_le (by norm_num)).contDiffAt)]

end OAI.Analysis.PDE.Dirichlet
