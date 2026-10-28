import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber

/-! # Pushforward Prescribed Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardPrescribedFiber

noncomputable section

/-! A pushforward coefficient with exactly one prescribed nonzero
branch in its fiber. Other branches may exist and have coefficient zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem coefficient {X Y : Scheme} (f : X ⟶ Y) (c : X →₀ ℚ) (x : X) (y : Y) (r : ℚ)
    (h : ∀ z : X, f z = y → c z = if z = x then r else 0) :
    CyclePushforward.pointPushforward f c y = if f x = y then r * (f.residueDegree x : ℚ) else 0 := by
  by_cases he : f x = y
  · rw [ite_eq_left he, CyclePushforward.pointPushforward, Finsupp.linearCombination_apply, Finsupp.sum_apply]
    rw [Finsupp.sum_eq_single x]
    · rw [Finsupp.smul_apply, he, Finsupp.single_eq_same, h x he, ite_eq_left rfl]
      rfl
    · intro z _ hzx
      by_cases hz : f z = y
      · rw [h z hz, ite_eq_right hzx, zero_smul, Finsupp.zero_apply]
      · rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (fun h => hz h.symm), smul_zero]
    · intro _
      simp only [zero_smul, Finsupp.zero_apply]
  · rw [ite_eq_right he]
    apply PushforwardFiber.pointPushforward_apply_eq_zero
    intro z hz hzy
    have hzx : z ≠ x := by rintro rfl; exact he hzy
    exact hz ((h z hzy).trans (ite_eq_right hzx))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardPrescribedFiber
