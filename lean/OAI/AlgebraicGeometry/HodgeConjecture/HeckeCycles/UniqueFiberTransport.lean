import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences

/-! # Unique Fiber Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UniqueFiberTransport.CM

/-! Unique lifts can be expressed on the actual source fiber and
transported through an equivalence that preserves an injective invariant. -/

open _root_.CategoryTheory

theorem subtype_iff {I : Type*} {P : I → Prop} (Q : Subtype P → Prop) :
    (∃! i : I, ∃ h : P i, Q ⟨i, h⟩) ↔ ∃! i : Subtype P, Q i := by
  constructor
  · rintro ⟨i, ⟨hi, hQ⟩, hu⟩
    refine ⟨⟨i, hi⟩, hQ, ?_⟩
    intro j hj
    exact Subtype.ext (hu j.val ⟨j.property, hj⟩)
  · rintro ⟨i, hi, hu⟩
    refine ⟨i.val, ⟨i.property, hi⟩, ?_⟩
    rintro j ⟨hj, hQ⟩
    exact congrArg Subtype.val (hu ⟨j, hj⟩ hQ)

theorem of_equivalence {I J A B : Type*} (e : I ≃ J) (f : I → A) (g : J → B)
    (t : B → A) (ht : Function.Injective t) (h : ∀ i, f i = t (g (e i)))
    (b : B) (hg : ∃! j, g j = b) : ∃! i, f i = t b := by
  obtain ⟨j, hj, hu⟩ := hg
  refine ⟨e.symm j, ?_, ?_⟩
  · change f (e.symm j) = t b
    rw [h, e.apply_symm_apply, hj]
  · intro i hi
    have hi' : g (e i) = b := ht ((h i).symm.trans hi)
    exact e.injective ((hu (e i) hi').trans (e.apply_symm_apply j).symm)

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UniqueFiberTransport.CM
