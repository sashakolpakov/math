import Mathlib

open Set _root_.MeasureTheory Matrix
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

variable {d : ℕ}

def normalScale (k : Fin d) (a : ℝ) : (Fin d→ℝ)→L[ℝ] (Fin d→ℝ) :=
  ContinuousLinearMap.pi (fun i ↦ (if i=k then a else 1) • ContinuousLinearMap.proj i)

@[simp] theorem normalScale_apply (k : Fin d) (a : ℝ) (x : Fin d→ℝ) (i : Fin d) :
    normalScale k a x i=(if i=k then a else 1)*x i := rfl

@[simp] theorem normalScale_apply_same (k : Fin d) (a : ℝ) (x : Fin d→ℝ) :
    normalScale k a x k=a*x k := by simp

theorem normalScale_apply_ne (k : Fin d) (a : ℝ) (x : Fin d→ℝ) {i : Fin d} (hi : i≠k) :
    normalScale k a x i=x i := by simp [hi]

@[simp] theorem normalScale_one (k : Fin d) (x : Fin d→ℝ) : normalScale k 1 x=x := by
  ext i
  simp

theorem normalScale_comp (k : Fin d) (a b : ℝ) (x : Fin d→ℝ) :
    normalScale k a (normalScale k b x)=normalScale k (a*b) x := by
  ext i
  by_cases hi : i=k <;> simp [hi,mul_assoc]

def normalScaleEquiv (k : Fin d) (a : ℝ) (ha : a≠0) : (Fin d→ℝ)≃L[ℝ] (Fin d→ℝ) where
  toLinearEquiv :=
    { toFun := normalScale k a
      invFun := normalScale k a⁻¹
      map_add' := (normalScale k a).map_add
      map_smul' := (normalScale k a).map_smul
      left_inv := fun x ↦ by rw [normalScale_comp,inv_mul_cancel₀ ha,normalScale_one]
      right_inv := fun x ↦ by rw [normalScale_comp,mul_inv_cancel₀ ha,normalScale_one] }
  continuous_toFun := (normalScale k a).continuous
  continuous_invFun := (normalScale k a⁻¹).continuous

theorem normalScale_matrix (k : Fin d) (a : ℝ) :
    (normalScale k a : (Fin d→ℝ)→(Fin d→ℝ))=
      Matrix.toLin' (Matrix.diagonal (fun i : Fin d ↦ if i=k then a else 1)) := by
  funext x
  ext i
  simp [Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Matrix.diagonal_apply,ite_mul]

theorem normalScale_matrix_det (k : Fin d) (a : ℝ) :
    Matrix.det (Matrix.diagonal (fun i : Fin d ↦ if i=k then a else 1))=a := by
  simp [Matrix.det_diagonal]

theorem map_volume_normalScale (k : Fin d) {a : ℝ} (ha : a≠0) :
    Measure.map (normalScale k a) volume=ENNReal.ofReal |a⁻¹| • volume := by
  rw [normalScale_matrix]
  have hdet := normalScale_matrix_det k a
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (by rw [hdet]; exact ha),hdet]

theorem normalScale_single (k i : Fin d) (a : ℝ) :
    normalScale k a (Pi.single i 1)=(if i=k then a else 1) • Pi.single i 1 := by
  ext j
  by_cases hj : j=i
  · subst j
    simp
  · simp [hj]

theorem normalScale_on_boundary (k : Fin d) (a : ℝ) {x : Fin d→ℝ} (hx : x k=0) :
    normalScale k a x=x := by
  ext i
  by_cases hi : i=k <;> simp [hi,hx]

end OAI.Analysis.Normed.Function.Sobolev
