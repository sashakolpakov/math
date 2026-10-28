import OAI.Analysis.PDE.Dirichlet.Hessian

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix MatrixOrder

/-- The quaternion-valued quadratic form, with multiplication order fixed. -/
def quaternionForm {m : ℕ} (A : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (z : Fin m → Quaternion ℝ) : Quaternion ℝ :=
  ∑ i, ∑ j, star (z i) * A i j * z j

theorem quaternionForm_add {m : ℕ} (A B : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (z : Fin m → Quaternion ℝ) : quaternionForm (A + B) z =
      quaternionForm A z + quaternionForm B z := by
  simp [quaternionForm, mul_add, add_mul, Finset.sum_add_distrib]

theorem quaternionForm_sum {m : ℕ} {ι : Type*} (t : Finset ι)
    (A : ι → Matrix (Fin m) (Fin m) (Quaternion ℝ)) (z : Fin m → Quaternion ℝ) :
    quaternionForm (∑ k ∈ t, A k) z = ∑ k ∈ t, quaternionForm (A k) z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [quaternionForm]
  | @insert k t hk ih => simp [hk, quaternionForm_add, ih]

theorem hessianMap_sum {m s : ℕ} {ι : Type*} (t : Finset ι)
    (e : Fin s → Quaternion ℝ) (A : ι → Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ) :
    OAI.Analysis.Calculus.Quaternion.hessianMap e (∑ k ∈ t, A k) = ∑ k ∈ t, OAI.Analysis.Calculus.Quaternion.hessianMap e (A k) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    apply Matrix.ext
    intro i j
    simp [OAI.Analysis.Calculus.Quaternion.hessianMap]
  | @insert k t hk ih => simp [hk, OAI.Analysis.Calculus.Quaternion.hessianMap_add, ih]

theorem quaternionForm_outer_nonneg {m : ℕ} (g z : Fin m → Quaternion ℝ) :
    0 ≤ (quaternionForm (OAI.Analysis.Calculus.Quaternion.outer g) z).re := by
  simpa only [quaternionForm, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    using OAI.Analysis.Calculus.Quaternion.outer_quadratic_nonneg g z

/-- The quaternionic Hessian map preserves positivity of a real Hessian. -/
theorem hessianMap_nonneg {m s : ℕ} (e : Fin s → Quaternion ℝ)
    {H : Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ} (hH : H.PosSemidef)
    (z : Fin m → Quaternion ℝ) : 0 ≤ (quaternionForm (OAI.Analysis.Calculus.Quaternion.hessianMap e H) z).re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  rw [Matrix.star_eq_conjTranspose]
  have hC : Cᴴ * C = ∑ k, Matrix.of (fun i j ↦ C k i * C k j) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.sum_apply]
  rw [hC, hessianMap_sum]
  have hrow (k : Fin m × Fin s) :
      OAI.Analysis.Calculus.Quaternion.hessianMap e (Matrix.of (fun i j ↦ C k i * C k j)) =
        OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap e (fun i ↦ C k i)) := OAI.Analysis.Calculus.Quaternion.hessianMap_rankOne e (fun i ↦ C k i)
  simp_rw [hrow]
  rw [quaternionForm_sum]
  have hre : (∑ k, quaternionForm (OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap e (fun i ↦ C k i))) z).re =
      ∑ k, (quaternionForm (OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap e (fun i ↦ C k i))) z).re := by
    let F : Fin m × Fin s → Quaternion ℝ := fun k ↦
      quaternionForm (OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap e (fun i ↦ C k i))) z
    change (∑ k, F k).re = ∑ k, (F k).re
    generalize (Finset.univ : Finset (Fin m × Fin s)) = t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert k t hk ih => simp [hk, ih]
  rw [hre]
  exact Finset.sum_nonneg fun k _ ↦ quaternionForm_outer_nonneg _ _

theorem quaternionHessian_nonpos_of_localMax {m s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : CoordinateSpace m s → ℝ} {x : CoordinateSpace m s}
    (hf : ContDiff ℝ 2 f) (hmax : IsLocalMax f x) (z : Fin m → Quaternion ℝ) :
    (quaternionForm (quaternionHessian e f x) z).re ≤ 0 := by
  have h := hessianMap_nonneg e (realHessian_neg_posSemidef_of_localMax hf hmax) z
  have hn : OAI.Analysis.Calculus.Quaternion.hessianMap e (-realHessian f x) = -quaternionHessian e f x := by
    apply Matrix.ext
    intro i j
    simp [OAI.Analysis.Calculus.Quaternion.hessianMap, quaternionHessian, Finset.sum_neg_distrib]
  rw [hn] at h
  simpa [quaternionForm, mul_neg, neg_mul, Finset.sum_neg_distrib] using h

theorem hessianMap_one {m s : ℕ} (e : Fin s → Quaternion ℝ)
    (he : ∀ α, e α * star (e α) = 1) :
    OAI.Analysis.Calculus.Quaternion.hessianMap (m := Fin m) e (1 : Matrix (Fin m × Fin s) (Fin m × Fin s) ℝ) =
      s • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [OAI.Analysis.Calculus.Quaternion.hessianMap, Matrix.one_apply, he]
  · simp [OAI.Analysis.Calculus.Quaternion.hessianMap, hij]

/-- The exact quadratic barrier Hessian used in the four-slot Dirichlet estimates. -/
theorem quaternionHessian_four_norm_sq {m : ℕ} (x : CoordinateSpace m 4) :
    quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y : CoordinateSpace m 4 ↦ ‖y‖ ^ 2) x =
      (8 : ℝ) • (1 : Matrix (Fin m) (Fin m) (Quaternion ℝ)) := by
  have he (α : Fin 4) : OAI.Analysis.Calculus.Quaternion.fourSlots α * star (OAI.Analysis.Calculus.Quaternion.fourSlots α) = 1 := by
    fin_cases α <;> ext <;> norm_num [OAI.Analysis.Calculus.Quaternion.fourSlots, Quaternion.re_mul]
  unfold quaternionHessian
  rw [realHessian_norm_sq, OAI.Analysis.Calculus.Quaternion.hessianMap_smul, hessianMap_one OAI.Analysis.Calculus.Quaternion.fourSlots he]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

end OAI.Analysis.PDE.Dirichlet
