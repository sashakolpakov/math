import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Point Affine -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointAffine

noncomputable section

/-! Every field-valued point of an arbitrary scheme is an affine morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem fieldPoint_isAffineHom {K : Type u} [Field K] {X : Scheme.{u}}
    (a : Spec (.of K) ⟶ X) : IsAffineHom a := by
  constructor
  intro U _
  by_cases h : Nonempty (a ⁻¹ᵁ U)
  · obtain ⟨x⟩ := h
    have he : a ⁻¹ᵁ U = ⊤ := by
      apply top_unique
      intro y _
      exact (Subsingleton.elim x.val y) ▸ x.property
    exact (congrArg IsAffineOpen he).mpr (isAffineOpen_top (Spec (.of K)))
  · have he : a ⁻¹ᵁ U = ⊥ := by
      apply le_antisymm
      · intro x hx
        exact (h ⟨⟨x, hx⟩⟩).elim
      · exact bot_le
    exact (congrArg IsAffineOpen he).mpr (isAffineOpen_bot (Spec (.of K)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.PointAffine
