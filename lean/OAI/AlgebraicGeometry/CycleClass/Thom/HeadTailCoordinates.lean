import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.ProductCoordinates

/-! # Head Tail Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.HeadTailCoordinates.Constructions

noncomputable section

/-! Literal complex head-and-tail coordinates using Fin.cons. -/

def headTailCoordinates (n : ℕ) : ((Fin 1 → ℂ) × (Fin n → ℂ)) ≃L[ℂ] (Fin (n + 1) → ℂ) where
  toFun v := Fin.cons (v.1 0) v.2
  invFun w := (fun _ => w 0, fun i => w i.succ)
  left_inv v := by
    apply Prod.ext
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · rfl
  right_inv w := by
    funext i
    cases i using Fin.cases <;> rfl
  map_add' v w := by
    funext i
    cases i using Fin.cases <;> rfl
  map_smul' a v := by
    funext i
    cases i using Fin.cases <;> rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero =>
      change Continuous (fun v : (Fin 1 → ℂ) × (Fin n → ℂ) => v.1 0)
      exact (continuous_apply 0).comp continuous_fst
    | succ j =>
      change Continuous (fun v : (Fin 1 → ℂ) × (Fin n → ℂ) => v.2 j)
      exact (continuous_apply j).comp continuous_snd
  continuous_invFun := (continuous_pi (fun _ => continuous_apply 0)).prodMk
    (continuous_pi (fun i => continuous_apply i.succ))

theorem headTailCoordinates_zero (n : ℕ) (v : (Fin 1 → ℂ) × (Fin n → ℂ)) :
    headTailCoordinates n v 0 = v.1 0 := rfl

theorem headTailCoordinates_succ (n : ℕ) (v : (Fin 1 → ℂ) × (Fin n → ℂ)) (i : Fin n) :
    headTailCoordinates n v i.succ = v.2 i := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.HeadTailCoordinates.Constructions
