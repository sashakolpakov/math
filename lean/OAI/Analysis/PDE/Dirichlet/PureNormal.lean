import OAI.Analysis.PDE.Dirichlet.NormalBounded
import OAI.Analysis.PDE.Dirichlet.HessianMapNorm
import OAI.Analysis.PDE.Dirichlet.Boundary.Hessian

open scoped Matrix Matrix.Norms.Elementwise InnerProductSpace

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem inner_coordinateVector {n s : ℕ} (ν : CoordinateSpace n s) (i : Fin n × Fin s) :
    ⟪ν, coordinateVector i⟫_ℝ = ν i := by
  simp [coordinateVector, EuclideanSpace.inner_single_right]

def realNormalRemainder {n s : ℕ} (ψ : CoordinateSpace n s → ℝ)
    (x ν : CoordinateSpace n s) : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ :=
  fun i j ↦ realHessian ψ x i j - fderiv ℝ (fderiv ℝ ψ) x ν ν * ν i * ν j

theorem realNormalRemainder_isSymm {n s : ℕ} {ψ : CoordinateSpace n s → ℝ}
    {x : CoordinateSpace n s} (hψ : ContDiffAt ℝ 2 ψ x) (ν : CoordinateSpace n s) :
    (realNormalRemainder ψ x ν).IsSymm := by
  have hH := realHessian_isSymm hψ
  apply Matrix.ext
  intro i j
  have hij := congrFun (congrFun hH i) j
  change realHessian ψ x j i = realHessian ψ x i j at hij
  change realHessian ψ x j i - _ * ν j * ν i = realHessian ψ x i j - _ * ν i * ν j
  rw [hij]
  ring

theorem quaternionHessian_normal_split {n s : ℕ} (e : Fin s → Q)
    (ψ : CoordinateSpace n s → ℝ) (x ν : CoordinateSpace n s) :
    quaternionHessian e ψ x = OAI.Analysis.Calculus.Quaternion.hessianMap e (realNormalRemainder ψ x ν) +
      fderiv ℝ (fderiv ℝ ψ) x ν ν • OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap e ν) := by
  have heq : realHessian ψ x = realNormalRemainder ψ x ν +
      fderiv ℝ (fderiv ℝ ψ) x ν ν • (Matrix.of (fun i j ↦ ν i * ν j)) := by
    apply Matrix.ext
    intro i j
    simp only [realNormalRemainder, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    ring
  rw [quaternionHessian, heq, OAI.Analysis.Calculus.Quaternion.hessianMap_add, OAI.Analysis.Calculus.Quaternion.hessianMap_smul]
  change OAI.Analysis.Calculus.Quaternion.hessianMap e (realNormalRemainder ψ x ν) +
    fderiv ℝ (fderiv ℝ ψ) x ν ν • OAI.Analysis.Calculus.Quaternion.hessianMap e (fun i j ↦ ν i * ν j) = _
  rw [OAI.Analysis.Calculus.Quaternion.hessianMap_rankOne]

theorem realNormalRemainder_norm_le {n s : ℕ} {ψ : CoordinateSpace n s → ℝ}
    {x ν : CoordinateSpace n s} (hψ : ContDiffAt ℝ 2 ψ x) (hν : ‖ν‖ = 1)
    {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (ht : ∀ v w, ⟪ν, v⟫_ℝ = 0 → ⟪ν, w⟫_ℝ = 0 →
      |fderiv ℝ (fderiv ℝ ψ) x v w| ≤ T * ‖v‖ * ‖w‖)
    (hm : ∀ v, ⟪ν, v⟫_ℝ = 0 → |fderiv ℝ (fderiv ℝ ψ) x ν v| ≤ M * ‖v‖) :
    ‖realNormalRemainder ψ x ν‖ ≤ 4 * T + 4 * M := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  have h := normal_remainder_abs_bound (fderiv ℝ (fderiv ℝ ψ) x) hν
    (le_of_eq (norm_coordinateVector i)) (le_of_eq (norm_coordinateVector j))
    (hψ.isSymmSndFDerivAt (by norm_num)).eq hT hM ht hm
  simpa only [realNormalRemainder, realHessian, Real.norm_eq_abs, inner_coordinateVector] using h

theorem quaternionForm_outer_tangent {n : ℕ} (ν z : Fin n → Q)
    (h : quaternionPairing ν z = 0) : quaternionForm (OAI.Analysis.Calculus.Quaternion.outer ν) z = 0 := by
  change quaternionForm (Matrix.of (fun i j ↦ ν i * star (ν j))) z = 0
  rw [quaternionForm_tensor]
  change (∑ i, star (z i) * ν i) * quaternionPairing ν z = 0
  rw [h, mul_zero]

/-- The pure real normal-normal Hessian estimate. All inputs other than
the determinant are tangential or mixed estimates; no full Hessian bound
or assumed solution operator occurs among the hypotheses. -/
theorem pure_normal_hessian_bound (n : ℕ) (T M c F : ℝ)
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : CoordinateSpace (n + 1) 4 → ℝ)
      (x ν : CoordinateSpace (n + 1) 4),
      ContDiffAt ℝ 2 ψ x → ‖ν‖ = 1 →
      (∀ v w, ⟪ν, v⟫_ℝ = 0 → ⟪ν, w⟫_ℝ = 0 →
        |fderiv ℝ (fderiv ℝ ψ) x v w| ≤ T * ‖v‖ * ‖w‖) →
      (∀ v, ⟪ν, v⟫_ℝ = 0 → |fderiv ℝ (fderiv ℝ ψ) x ν v| ≤ M * ‖v‖) →
      (∀ z, quaternionPairing (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots ν) z = 0 →
        c * (quaternionForm 1 z).re ≤ (quaternionForm (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) z).re) →
      |OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)| ≤ F →
      |fderiv ℝ (fderiv ℝ ψ) x ν ν| ≤ C := by
  let K := hessianMapBound (n := n + 1) OAI.Analysis.Calculus.Quaternion.fourSlots * (4 * T + 4 * M)
  let L := ‖gradientCoordinateCLM (n := n + 1) OAI.Analysis.Calculus.Quaternion.fourSlots‖
  obtain ⟨C, hC, hbound⟩ := normal_parameter_bound_of_bounded_data n K L c F hc
  refine ⟨C, hC, ?_⟩
  intro ψ x ν hψ hν ht hm htq hdet
  let A := OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (realNormalRemainder ψ x ν)
  let g := OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots ν
  have hA : ‖A‖ ≤ K := (hessianMap_norm_le OAI.Analysis.Calculus.Quaternion.fourSlots _).trans
    (mul_le_mul_of_nonneg_left (realNormalRemainder_norm_le hψ hν hT hM ht hm)
      (hessianMapBound_nonneg OAI.Analysis.Calculus.Quaternion.fourSlots))
  have hg : ‖g‖ ≤ L := by simpa only [g, L, hν, mul_one] using gradientMap_norm_le OAI.Analysis.Calculus.Quaternion.fourSlots ν
  have hAH : A.IsHermitian := OAI.Analysis.Calculus.Quaternion.hessianMap_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots _ (realNormalRemainder_isSymm hψ ν)
  have hunit : quaternionPairing g g = 1 := by
    simpa only [g, hν, one_pow, one_smul] using quaternionPairing_gradient_self ν
  have hsplit := quaternionHessian_normal_split OAI.Analysis.Calculus.Quaternion.fourSlots ψ x ν
  have hcoercive : ∀ z, quaternionPairing g z = 0 →
      c * (quaternionForm 1 z).re ≤ (quaternionForm A z).re := by
    intro z hz
    have h := htq z hz
    rw [hsplit, quaternionForm_add, quaternionForm_smul_matrix,
      quaternionForm_outer_tangent _ _ hz, smul_zero, add_zero] at h
    exact h
  apply hbound A g _ hA hg hAH hunit hcoercive
  simpa only [A, g, ← hsplit] using hdet

end OAI.Analysis.PDE.Dirichlet
