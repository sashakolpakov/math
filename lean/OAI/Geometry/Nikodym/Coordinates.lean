import OAI.Analysis.Fourier.Estimates

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set
namespace OAI.Geometry.Nikodym

def projectiveJoinLinear (d : ℕ) : (Space d × ℝ) ≃ₗ[ℝ] Space (d+1) where
  toFun p := WithLp.toLp 2 (Fin.cases p.2 (fun i => p.1 i))
  invFun x := (WithLp.toLp 2 (fun i => x i.succ),x 0)
  map_add' p q := by ext i; cases i using Fin.cases <;> rfl
  map_smul' c p := by ext i; cases i using Fin.cases <;> rfl
  left_inv p := by
    apply Prod.ext
    · ext i
      rfl
    · rfl
  right_inv x := by ext i; cases i using Fin.cases <;> rfl

def projectiveJoin (d : ℕ) : (Space d × ℝ) ≃L[ℝ] Space (d+1) :=
  (projectiveJoinLinear d).toContinuousLinearEquiv

@[simp] theorem projectiveJoin_zero (d : ℕ) (p : Space d × ℝ) :
    projectiveJoin d p 0 = p.2 := rfl

@[simp] theorem projectiveJoin_succ (d : ℕ) (p : Space d × ℝ) (i : Fin d) :
    projectiveJoin d p i.succ = p.1 i := rfl

@[simp] theorem projectiveJoin_symm_first (d : ℕ) (x : Space (d+1)) (i : Fin d) :
    ((projectiveJoin d).symm x).1 i = x i.succ := rfl

@[simp] theorem projectiveJoin_symm_second (d : ℕ) (x : Space (d+1)) :
    ((projectiveJoin d).symm x).2 = x 0 := rfl

theorem projectiveJoin_norm_sq (d : ℕ) (p : Space d × ℝ) :
    ‖projectiveJoin d p‖^2 = ‖p.1‖^2 + |p.2|^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ,EuclideanSpace.real_norm_sq_eq]
  simp only [projectiveJoin_zero,projectiveJoin_succ,sq_abs]
  ring

theorem projectiveJoin_norm_le (d : ℕ) (p : Space d × ℝ) :
    ‖projectiveJoin d p‖ ≤ ‖p.1‖+|p.2| := by
  have h := projectiveJoin_norm_sq d p
  nlinarith [norm_nonneg (projectiveJoin d p),norm_nonneg p.1,abs_nonneg p.2,
    mul_nonneg (norm_nonneg p.1) (abs_nonneg p.2)]

theorem norm_projectiveJoin_le_two (d : ℕ) :
    ‖(projectiveJoin d : (Space d × ℝ) →L[ℝ] Space (d+1))‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound (f := (projectiveJoin d).toContinuousLinearMap) (by norm_num)
  intro p
  apply (projectiveJoin_norm_le d p).trans
  rw [Prod.norm_def,Real.norm_eq_abs]
  nlinarith [le_max_left ‖p.1‖ |p.2|,le_max_right ‖p.1‖ |p.2|]

theorem projectiveJoin_symm_norm_le (d : ℕ) (x : Space (d+1)) :
    ‖(projectiveJoin d).symm x‖ ≤ ‖x‖ := by
  have h := projectiveJoin_norm_sq d ((projectiveJoin d).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  rw [Prod.norm_def,Real.norm_eq_abs]
  apply max_le <;> nlinarith [norm_nonneg x,norm_nonneg ((projectiveJoin d).symm x).1,
    abs_nonneg ((projectiveJoin d).symm x).2,sq_nonneg ‖((projectiveJoin d).symm x).1‖,
    sq_nonneg |((projectiveJoin d).symm x).2|]

theorem norm_projectiveJoin_symm_le_one (d : ℕ) :
    ‖((projectiveJoin d).symm : Space (d+1) →L[ℝ] (Space d × ℝ))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (f := (projectiveJoin d).symm.toContinuousLinearMap) zero_le_one
  intro x
  simpa only [one_mul] using! projectiveJoin_symm_norm_le d x

end OAI.Geometry.Nikodym
