import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Module.Submodule.Union

/-! # Regular Linear Forms -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RegularLinearForms.Construction

noncomputable section

/-! A regular point avoids all nonzero members of a finite family
of linear forms. Opposite pairs then make the positive forms separating. -/

open scoped Classical

theorem exists_regular_linear_forms
    {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Finite ι]
    (w : ι → Module.Dual ℝ E) : ∃ H : E, ∀ i, w i H = 0 ↔ w i = 0 := by
  let J := {i : ι // w i ≠ 0}
  have hn (i : J) : ∃ x, w i.val x ≠ 0 := by
    by_contra! h
    apply i.property
    exact LinearMap.ext h
  obtain ⟨H, hH⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun i : J => w i.val) hn
  refine ⟨H, fun i => ⟨fun hi => ?_, fun hi => by rw [hi]; rfl⟩⟩
  by_contra hn
  exact hH ⟨i, hn⟩ hi

theorem positive_linear_forms_separate
    {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (w : ι → Module.Dual ℝ E)
    (hsep : ∀ x, (∀ i, w i x = 0) → x = 0)
    (hopp : ∀ i, ∃ j, w j = -w i)
    (H : E) (hreg : ∀ i, w i H = 0 ↔ w i = 0) :
    ∀ x, (∀ i : {i : ι // 0 < w i H}, w i.val x = 0) → x = 0 := by
  intro x hx
  apply hsep x
  intro i
  rcases lt_trichotomy (w i H) 0 with hneg | hzero | hpos
  · obtain ⟨j, hj⟩ := hopp i
    have hp : 0 < w j H := by simpa only [hj, LinearMap.neg_apply, neg_pos] using hneg
    have hz := hx ⟨j, hp⟩
    simpa only [hj, LinearMap.neg_apply, neg_eq_zero] using hz
  · rw [(hreg i).mp hzero]
    rfl
  · exact hx ⟨i, hpos⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RegularLinearForms.Construction
