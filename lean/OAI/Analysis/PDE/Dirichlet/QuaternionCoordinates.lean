import OAI.Analysis.PDE.Dirichlet.Covariance
import OAI.Analysis.PDE.Dirichlet.RigidMotion
import OAI.Analysis.PDE.Dirichlet.Symbol
import Mathlib.Analysis.InnerProductSpace.Dual

open scoped Matrix RealInnerProductSpace

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

theorem realRepresentation_conjTranspose {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    realRepresentation Aᴴ = (realRepresentation A)ᵀ := by
  ext i j
  change (star (OAI.Analysis.Calculus.Quaternion.fourSlots i.2) * star (A j.1 i.1) * OAI.Analysis.Calculus.Quaternion.fourSlots j.2).re =
    (star (OAI.Analysis.Calculus.Quaternion.fourSlots j.2) * A j.1 i.1 * OAI.Analysis.Calculus.Quaternion.fourSlots i.2).re
  rw [← Quaternion.re_star (star (OAI.Analysis.Calculus.Quaternion.fourSlots j.2) * A j.1 i.1 * OAI.Analysis.Calculus.Quaternion.fourSlots i.2)]
  simp only [star_mul, star_star, mul_assoc]

theorem realRepresentation_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    realRepresentation (-A) = -realRepresentation A := by
  ext i j
  simp [realRepresentation]

theorem realRepresentation_skew {n : ℕ} {A : Matrix (Fin n) (Fin n) Q}
    (hA : Aᴴ = -A) : (realRepresentation A)ᵀ = -realRepresentation A := by
  rw [← realRepresentation_conjTranspose, hA, realRepresentation_neg]

theorem slotMatrix_mul_realRepresentation {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    slotMatrix n 4 OAI.Analysis.Calculus.Quaternion.fourSlots * realLift (realRepresentation A) =
      A * slotMatrix n 4 OAI.Analysis.Calculus.Quaternion.fourSlots := by
  have h := congrArg Matrix.conjTranspose (realRepresentation_mul_starSlot Aᴴ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, ← realLift_transpose,
    realRepresentation_conjTranspose, Matrix.transpose_transpose] at h
  exact h

def realVectorLift {ι : Type*} (x : ι → ℝ) : ι → Q := fun i ↦ algebraMap ℝ Q (x i)

theorem gradientMap_eq_slot_action {n : ℕ} (x : Fin n × Fin 4 → ℝ) :
    OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots x = slotMatrix n 4 OAI.Analysis.Calculus.Quaternion.fourSlots *ᵥ realVectorLift x := by
  funext i
  simp [OAI.Analysis.Calculus.Quaternion.gradientMap, slotMatrix, realVectorLift, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro α _
  change x (i, α) • OAI.Analysis.Calculus.Quaternion.fourSlots α = OAI.Analysis.Calculus.Quaternion.fourSlots α * algebraMap ℝ Q (x (i, α))
  rw [Algebra.smul_def]
  exact Algebra.commutes (x (i, α)) (OAI.Analysis.Calculus.Quaternion.fourSlots α)

theorem realVectorLift_action {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    realVectorLift (realMatrixAction B x) = realLift B *ᵥ realVectorLift x := by
  funext i
  have hi := congrFun (Matrix.ofLp_toEuclideanCLM B x) i
  change algebraMap ℝ Q ((realMatrixAction B x) i) = _
  rw [show (realMatrixAction B x) i = (B *ᵥ x) i from hi]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, realLift, Matrix.map_apply,
    realVectorLift]

/-- The coordinate matrix acts on real four-slot vectors by genuine left
quaternionic multiplication. -/
theorem gradientMap_realMatrixAction {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (x : CoordinateSpace n 4) :
    OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots (realMatrixAction (realRepresentation A) x) =
      A *ᵥ OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots x := by
  rw [gradientMap_eq_slot_action, realVectorLift_action,
    Matrix.mulVec_mulVec, slotMatrix_mul_realRepresentation,
    ← Matrix.mulVec_mulVec, ← gradientMap_eq_slot_action]

theorem quaternionPairing_gradient_re {n : ℕ} (x y : CoordinateSpace n 4) :
    (quaternionPairing (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots x) (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots y)).re =
      ⟪x, y⟫ := by
  rw [quaternionPairing, quaternion_re_sum]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_prod_type,
    Fin.sum_univ_four]
  apply Finset.sum_congr rfl
  intro i _
  simp [OAI.Analysis.Calculus.Quaternion.gradientMap_fourSlots]
  ; ring

theorem quaternionPairing_gradient_self {n : ℕ} (x : CoordinateSpace n 4) :
    quaternionPairing (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots x) (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots x) =
      ‖x‖ ^ 2 • (1 : Q) := by
  let q := quaternionPairing (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots x) (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots x)
  have hs : star q = q := star_quaternionPairing _ _
  have hI : q.imI = 0 := by
    have h := congrArg (fun a : Q ↦ a.imI) hs
    change -q.imI = q.imI at h
    linarith
  have hJ : q.imJ = 0 := by
    have h := congrArg (fun a : Q ↦ a.imJ) hs
    change -q.imJ = q.imJ at h
    linarith
  have hK : q.imK = 0 := by
    have h := congrArg (fun a : Q ↦ a.imK) hs
    change -q.imK = q.imK at h
    linarith
  have hR : q.re = ‖x‖ ^ 2 := by
    dsimp only [q]
    rw [quaternionPairing_gradient_re, real_inner_self_eq_norm_sq]
  change q = _
  ext <;> simp [hR, hI, hJ, hK]

/-- Real skew-adjointness of the infinitesimal quaternionic action. -/
theorem realMatrixAction_skew {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hB : Bᵀ = -B) (x y : EuclideanSpace ℝ ι) :
    ⟪x, realMatrixAction B y⟫ = -⟪realMatrixAction B x, y⟫ := by
  have hswap : ⟪realMatrixAction B x, y⟫ = ⟪y, realMatrixAction B x⟫ := real_inner_comm _ _
  rw [hswap]
  simp only [realMatrixAction, Matrix.inner_toEuclideanCLM, Matrix.mulVec, dotProduct,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij := congrFun (congrFun hB i) j
  change B j i = -B i j at hij
  rw [hij]
  ring

/-- Every real tangent vector is realized by a quaternionic infinitesimal
rotation of a unit real normal. -/
theorem exists_quaternionic_rotation {n : ℕ} (ν v : CoordinateSpace n 4)
    (hν : ‖ν‖ = 1) (hv : ⟪ν, v⟫ = 0) :
    ∃ A : Matrix (Fin n) (Fin n) Q, Aᴴ = -A ∧
      realMatrixAction (realRepresentation A) ν = v := by
  let qν := OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots ν
  let qv := OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots v
  have ht : (quaternionPairing qν qv).re = 0 := by
    dsimp only [qν, qv]
    rw [quaternionPairing_gradient_re, hv]
  have hu : quaternionPairing qν qν = 1 := by
    dsimp only [qν]
    rw [quaternionPairing_gradient_self, hν]
    simp
  refine ⟨rigidMotionMatrix qν qv, rigidMotionMatrix_skew qν qv ht, ?_⟩
  have hh : OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots
      (realMatrixAction (realRepresentation (rigidMotionMatrix qν qv)) ν) =
      OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots v := by
    rw [gradientMap_realMatrixAction, rigidMotionMatrix_normal qν qv hu ht]
  have heq := OAI.Analysis.Calculus.Quaternion.gradientMap_fourSlots_injective hh
  ext i
  exact congrFun heq i

end OAI.Analysis.PDE.Dirichlet
