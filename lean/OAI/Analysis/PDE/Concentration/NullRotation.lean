import OAI.Analysis.PDE.Concentration.CurrentCovariance

namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion Matrix
open scoped Matrix

private theorem fin_cases_one {d : ℕ} {β : Sort*} (a : β) (f : Fin (d + 1) → β) :
    Fin.cases a f (1 : Fin (d + 2)) = f 0 := by
  rw [← Fin.succ_zero_eq_one]
  rfl

/-- The manuscript's orthogonal change `(T,b,x) ↦ (t,s,x)`:
`t=(T+b)/sqrt 2`, `s=(b-T)/sqrt 2`. -/
noncomputable def nullRotation (d : ℕ) : Matrix (Fin (d + 2)) (Fin (d + 2)) ℝ :=
  Fin.cases
    (Fin.cases (Real.sqrt 2)⁻¹ (Fin.cases (Real.sqrt 2)⁻¹ (fun _ => 0)))
    (Fin.cases
      (Fin.cases (-(Real.sqrt 2)⁻¹) (Fin.cases (Real.sqrt 2)⁻¹ (fun _ => 0)))
      (fun i => Fin.cases 0 (Fin.cases 0 (fun j => if i = j then 1 else 0))))

theorem nullRotation_orthogonal (d : ℕ) : nullRotation d * (nullRotation d)ᵀ = 1 := by
  have hs : ((Real.sqrt 2)⁻¹) ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
      Fin.sum_univ_succ, nullRotation, fin_cases_one, pow_two, Fin.ext_iff] at *
  all_goals try simp only [← Fin.ext_iff]
  all_goals try simp
  all_goals nlinarith

theorem slot_action_apply {n s : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) (i : Fin n) (α : Fin s) :
    OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x (i, α) = ∑ j, R i j * x (j, α) := by
  simp [OAI.Analysis.PDE.Dirichlet.realMatrixAction, Matrix.mulVec, dotProduct, slotLift, Fintype.sum_prod_type,
    ite_mul]

theorem nullRotation_action_time {d s : ℕ} (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) s) (α : Fin s) :
    OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) x (0, α) =
      (x (0, α) + x (1, α)) / Real.sqrt 2 := by
  rw [slot_action_apply]
  simp [nullRotation, Fin.sum_univ_succ]
  ring

theorem nullRotation_action_longitudinal {d s : ℕ} (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) s) (α : Fin s) :
    OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) x (1, α) =
      (x (1, α) - x (0, α)) / Real.sqrt 2 := by
  rw [slot_action_apply]
  simp [nullRotation, Fin.sum_univ_succ, fin_cases_one]
  ring

theorem nullRotation_action_transverse {d s : ℕ} (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) s)
    (i : Fin d) (α : Fin s) :
    OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift (nullRotation d)) x (i.succ.succ, α) = x (i.succ.succ, α) := by
  rw [slot_action_apply]
  simp [nullRotation, Fin.sum_univ_succ]

end OAI.Analysis.PDE.Concentration
