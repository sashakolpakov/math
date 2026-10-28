import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ProjectionRestriction

/-! # Global Projective -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalProjective

noncomputable section

/-! When a graded map satisfies the irrelevant-ideal condition,
the glued rational projection is the restriction of the native Proj map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
  (hf : HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) ≤
    (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading m)).map f)

theorem map_eq : Projective.BasicOpen.RationalProjection.map f = (Projective.BasicOpen.RationalProjection.domain f).ι ≫ Proj.map f hf := by
  apply (Projective.BasicOpen.RationalProjection.cover f).hom_ext
  intro i
  change (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (Projective.BasicOpen.RationalProjection.coordinateOpen f) i) ≫ Projective.BasicOpen.RationalProjection.map f =
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (Projective.BasicOpen.RationalProjection.coordinateOpen f) i) ≫ ((Projective.BasicOpen.RationalProjection.domain f).ι ≫ Proj.map f hf)
  rw [Projective.BasicOpen.RationalProjection.chart_map, ← Category.assoc, Scheme.homOfLE_ι,
    Projective.LinearChart.Hom.chart, Projective.LinearChart.Hom.affine,
    ← Proj.awayι_comp_map f hf Nat.zero_lt_one (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i),
    Proj.awayι]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem restriction {S : Scheme} (i : S ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (hi : ∀ x, i x ∈ Projective.BasicOpen.RationalProjection.domain f) :
    Projective.ProjectionRestriction.projection f i hi = i ≫ Proj.map f hf := by
  rw [Projective.ProjectionRestriction.projection, map_eq f hf, ← Category.assoc,
    Projective.ProjectionRestriction.lift_fac]

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalProjective
