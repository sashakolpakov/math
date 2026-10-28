import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

/-! # Pushforward Fiber -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber

noncomputable section

/-! A proper-pushforward coefficient can be computed on a subspace that
covers its whole fiber and preserves the residue fields. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

universe u

theorem pointPushforward_apply_eq_zero {A B : Scheme.{u}} (f : A ⟶ B)
    (c : A →₀ ℚ) (x : B) (h : ∀ a : A, c a ≠ 0 → f a ≠ x) :
    CyclePushforward.pointPushforward f c x = 0 := by
  rw [CyclePushforward.pointPushforward, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne (h a (Finsupp.mem_support_iff.mp ha)).symm,
    smul_zero]

theorem pointPushforward_uniqueFiber {A B : Scheme.{u}} (f : A ⟶ B)
    (a : A) (x : B) (ha : f a = x) (hunique : ∀ b : A, f b = x → b = a) (c : A →₀ ℚ) :
    CyclePushforward.pointPushforward f c x = c a * (f.residueDegree a : ℚ) := by
  rw [CyclePushforward.pointPushforward, Finsupp.linearCombination_apply, Finsupp.sum_apply,
    Finsupp.sum_eq_single a]
  · rw [Finsupp.smul_apply, ha, Finsupp.single_eq_same]
    rfl
  · intro b _ hba
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne
      (fun h => hba (hunique b h.symm)), smul_zero]
  · intro _
    simp only [zero_smul, Finsupp.zero_apply]

theorem pointPushforward_coeff_of_fiber_cover {A B C : Scheme.{u}}
    (i : A ⟶ B) (f : B ⟶ C) (x : C) (hi : Function.Injective i)
    (hdegree : ∀ a : A, i.residueDegree a = 1)
    (hcover : ∀ b : B, f b = x → b ∈ Set.range i) (c : B →₀ ℚ) :
    CyclePushforward.pointPushforward f c x =
      CyclePushforward.pointPushforward (i ≫ f) (Finsupp.comapDomain i c hi.injOn) x := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [Finsupp.comapDomain_add_of_injective hi]
    simp only [map_add, Finsupp.add_apply, hc, hd]
  | single b r =>
    by_cases hb : b ∈ Set.range i
    · obtain ⟨a, rfl⟩ := hb
      rw [Finsupp.comapDomain_single, CyclePushforward.pointPushforward_single,
        CyclePushforward.pointPushforward_single, CyclePushforward.residueDegree_comp, hdegree, mul_one]
      rfl
    · have hfx : f b ≠ x := fun h => hb (hcover b h)
      rw [Finsupp.comapDomain_single_of_not_mem_range hb, map_zero, Finsupp.zero_apply,
        CyclePushforward.pointPushforward_single]
      exact Finsupp.single_eq_of_ne hfx.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber
