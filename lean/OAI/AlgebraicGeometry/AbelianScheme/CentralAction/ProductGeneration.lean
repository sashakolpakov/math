import Mathlib

/-! # Product Generation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ProductGeneration.Construction

/-! Componentwise generation by differences determines an additive
endomorphism of the entire finite product. -/

theorem end_eq_id_of_component_differences
    {I A : Type*} [Fintype I] [DecidableEq I] [AddCommGroup A]
    {B : I → Type*} [∀ i, AddCommGroup (B i)] {X : I → Type*}
    (e : A ≃+ ∀ i, B i) (a : ∀ i, X i → B i) (z : ∀ i, X i → A)
    (hz : ∀ i x, e (z i x) = Pi.single i (a i x))
    (hg : ∀ i, ∃ n : ℕ, Function.Surjective
      (fun w : Fin n → X i × X i => ∑ j, (a i (w j).1 - a i (w j).2)))
    (F : A →+ A) (hF : ∀ i x y, F (z i x - z i y) = z i x - z i y) :
    ∀ x, F x = x := by
  classical
  have haxis (i : I) (b : B i) : F (e.symm (Pi.single i b)) = e.symm (Pi.single i b) := by
    obtain ⟨n, hn⟩ := hg i
    obtain ⟨w, hw⟩ := hn b
    have he : e.symm (Pi.single i b) = ∑ j, (z i (w j).1 - z i (w j).2) := by
      apply e.injective
      rw [e.apply_symm_apply, map_sum]
      funext k
      by_cases h : i = k
      · subst k
        simpa only [Finset.sum_apply, map_sub, hz, Pi.sub_apply, Pi.single_eq_same] using hw.symm
      · simp only [Finset.sum_apply, map_sub, hz, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm h),
          sub_self, Finset.sum_const_zero]
    rw [he, map_sum]
    exact Finset.sum_congr rfl (fun j _ => hF i (w j).1 (w j).2)
  intro x
  have hx : (∑ i, e.symm (Pi.single i (e x i))) = x := by
    apply e.injective
    rw [map_sum]
    simp only [e.apply_symm_apply]
    exact Finset.univ_sum_single (e x)
  calc
    F x = F (∑ i, e.symm (Pi.single i (e x i))) := congrArg F hx.symm
    _ = ∑ i, F (e.symm (Pi.single i (e x i))) := map_sum F _ _
    _ = ∑ i, e.symm (Pi.single i (e x i)) := Finset.sum_congr rfl (fun i _ => haxis i (e x i))
    _ = x := hx

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ProductGeneration.Construction
