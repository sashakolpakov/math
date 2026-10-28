import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralIdempotents
import Mathlib.AlgebraicGeometry.Properties

/-! # Global Idempotent Ext -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalIdempotentExt.Construction

noncomputable section

/-! # Completion: global idempotents are determined by their nonzero loci -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- Two global idempotents coincide when their actual basic opens coincide. -/
theorem global_idempotent_ext {X : Scheme.{u}} {e f : Γ(X, ⊤)}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : X.basicOpen e = X.basicOpen f) : e = f := by
  apply TopCat.Presheaf.section_ext X.sheaf ⊤ e f
  intro x hx
  let φ := X.presheaf.germ ⊤ x hx
  have hm : IsUnit (φ e) ↔ IsUnit (φ f) := by
    simpa only [Scheme.mem_basicOpen_top] using
      (show x ∈ X.basicOpen e ↔ x ∈ X.basicOpen f by rw [h])
  rcases IntegralIdempotents.Construction.local_idempotent_eq_zero_or_one (X.presheaf.stalk x) (he.map φ.hom) with h₀ | h₁ <;>
    rcases IntegralIdempotents.Construction.local_idempotent_eq_zero_or_one (X.presheaf.stalk x) (hf.map φ.hom) with h₂ | h₃
  · exact h₀.trans h₂.symm
  · simp [h₀, h₃] at hm
  · simp [h₁, h₂] at hm
  · exact h₁.trans h₃.symm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalIdempotentExt.Construction
