import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduction

/-! # Closed Subscheme -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ClosedSubscheme

noncomputable section

/-! The reduced induced scheme on a closed subset is constructed from
its vanishing ideal; its underlying image is exactly that subset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_reduced_closedImmersion_with_range (S : Scheme.{0}) (W : Set S) (hW : IsClosed W) :
    ∃ Z : Over S, IsReduced Z.left ∧ IsClosedImmersion Z.hom ∧ Set.range Z.hom = W := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨W, hW⟩ : TopologicalSpace.Closeds S)
  let Y : Over S := Over.mk I.subschemeι
  let Z := Reduction.reduction Y
  have hclosed : IsClosedImmersion Z.hom :=
    inferInstanceAs (IsClosedImmersion ((Reduction.reductionι Y).left ≫ I.subschemeι))
  refine ⟨Z, inferInstance, hclosed, ?_⟩
  change Set.range (I.subschemeι ∘ (Reduction.reductionι Y).left) = W
  rw [Set.range_comp, Reduction.reduction_range, Set.image_univ, Scheme.IdealSheafData.range_subschemeι]
  exact Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨W, hW⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ClosedSubscheme
