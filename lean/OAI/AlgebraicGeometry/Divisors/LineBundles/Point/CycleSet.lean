import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Cycle Set -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleSet.BundleCycles

noncomputable section

/-! The linear operation retaining exactly the coefficients indexed by a set. -/

def pointCycleSetPart {α : Type} (S : Set α) : (α →₀ ℚ) →ₗ[ℚ] (α →₀ ℚ) := by
  classical
  exact { toFun := Finsupp.filter (· ∈ S)
          map_add' := fun _ _ => Finsupp.filter_add
          map_smul' := fun _ _ => Finsupp.filter_smul }

theorem pointCycleSetPart_apply_mem {α : Type} (S : Set α) (z : α →₀ ℚ) (x : α) (hx : x ∈ S) :
    pointCycleSetPart S z x = z x := by
  classical
  exact Finsupp.filter_apply_pos (· ∈ S) z hx

theorem pointCycleSetPart_apply_notMem {α : Type} (S : Set α) (z : α →₀ ℚ) (x : α) (hx : x ∉ S) :
    pointCycleSetPart S z x = 0 := by
  classical
  exact Finsupp.filter_apply_neg (· ∈ S) z hx

theorem pointCycleSetPart_single_mem {α : Type} (S : Set α) (x : α) (a : ℚ) (hx : x ∈ S) :
    pointCycleSetPart S (Finsupp.single x a) = Finsupp.single x a := by
  classical
  exact Finsupp.filter_single_of_pos (· ∈ S) hx

theorem pointCycleSetPart_single_notMem {α : Type} (S : Set α) (x : α) (a : ℚ) (hx : x ∉ S) :
    pointCycleSetPart S (Finsupp.single x a) = 0 := by
  classical
  exact Finsupp.filter_single_of_neg (· ∈ S) hx

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleSet.BundleCycles
