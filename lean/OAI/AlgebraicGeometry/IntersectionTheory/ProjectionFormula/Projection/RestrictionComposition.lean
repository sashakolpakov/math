import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ProjectionCoincidence

/-! # Restriction Composition -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.RestrictionComposition

noncomputable section

/-! The actual rational projective projection commutes with
restriction to any scheme whose image avoids its center. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem comp {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
    {T S : Scheme} (i : T ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (hi : ∀ x, i x ∈ Projective.BasicOpen.RationalProjection.domain f) (u : S ⟶ T)
    (hu : ∀ x, (u ≫ i) x ∈ Projective.BasicOpen.RationalProjection.domain f) :
    Projective.ProjectionRestriction.projection f (u ≫ i) hu =
      u ≫ Projective.ProjectionRestriction.projection f i hi := by
  unfold Projective.ProjectionRestriction.projection
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono (Projective.BasicOpen.RationalProjection.domain f).ι).mp
  rw [Projective.ProjectionRestriction.lift_fac, Category.assoc,
    Projective.ProjectionRestriction.lift_fac]

theorem restricted (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
    (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    {T : Scheme} (u : T ⟶ X.carrier)
    (hu : ∀ x, X.embedding (u x) ∈ Projective.BasicOpen.RationalProjection.domain (FiniteProjective.FromForms.coordinates X k L))
    (V : T.Opens) (hV : V ≤ u ⁻¹ᵁ PartialLinear.Projection.domain X k L) :
    u.resLE (PartialLinear.Projection.domain X k L) V hV ≫ PartialLinear.Projection.map X k L =
      V.ι ≫ Projective.ProjectionRestriction.projection (FiniteProjective.FromForms.coordinates X k L) (u ≫ X.embedding) hu := by
  unfold PartialLinear.Projection.map Projective.ProjectionRestriction.projection
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply (cancel_mono (Projective.BasicOpen.RationalProjection.domain (FiniteProjective.FromForms.coordinates X k L)).ι).mp
  rw [Category.assoc, Projective.ProjectionRestriction.lift_fac, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι, Category.assoc, Category.assoc, Projective.ProjectionRestriction.lift_fac]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.RestrictionComposition
