import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.RestrictionComposition
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ProjectionCoincidence

/-! # Defined Pair -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DefinedPair

noncomputable section

/-! The partial incidence locus is the actual equalizer whenever
the two maps of the pair scheme avoid the projection center. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
  (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (u v : T ⟶ X.toOver)
  (hu : ∀ x, u.left x ∈ PartialLinear.Projection.domain X k L)
  (hv : ∀ x, v.left x ∈ PartialLinear.Projection.domain X k L)

def projection : T ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k) :=
  Over.homMk (Projective.ProjectionRestriction.projection (Projection.FiniteProjective.FromForms.coordinates X k L)
    (u.left ≫ X.embedding) hu) (by
      change Projective.ProjectionRestriction.projection (Projection.FiniteProjective.FromForms.coordinates X k L)
        (u.left ≫ X.embedding) hu ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase k = T.hom
      rw [Projective.ProjectionRestriction.over_base _ _ _ (Projection.FiniteProjective.FromForms.constants X k L),
        Category.assoc, X.embedding_over]
      exact u.w)

theorem first_eq : (Projection.Coincidence.first X k L u v).left =
    (Projection.Coincidence.domain X k L u v).ι ≫ (projection X k L u hu).left :=
  Projection.RestrictionComposition.restricted X k L u.left hu _ inf_le_left

theorem second_eq : (Projection.Coincidence.second X k L u v).left =
    (Projection.Coincidence.domain X k L u v).ι ≫ (projection X k L v hv).left :=
  Projection.RestrictionComposition.restricted X k L v.left hv _ inf_le_right

variable [LocallyOfFiniteType T.hom]

theorem mem_iff_closed (x : T.left) (hx : IsClosed ({x} : Set T.left)) :
    x ∈ Projection.Coincidence.locus X k L u v ↔
      (projection X k L u hu).left x = (projection X k L v hv).left x := by
  let U := Projection.Coincidence.domain X k L u v
  let y : U := ⟨x, ⟨hu x, hv x⟩⟩
  have hset : U.ι ⁻¹' ({x} : Set T.left) = ({y} : Set (U : Scheme)) := by
    ext z
    change z.val = x ↔ z = y
    constructor
    · exact fun hz => Subtype.ext hz
    · rintro rfl
      rfl
  have hy : IsClosed ({y} : Set (U : Scheme)) := hset ▸ hx.preimage U.ι.continuous
  have he := Projection.Coincidence.mem_iff_closed X k L u v y hy
  rw [first_eq X k L u v hu, second_eq X k L u v hv] at he
  exact he

theorem locus_eq : Projection.Coincidence.locus X k L u v =
    Closed.Equalizer.locus (projection X k L u hu) (projection X k L v hv) := by
  apply le_antisymm
  · apply Projection.ProjectionCoincidence.closed_subset T.hom
    intro x hx hc
    exact Closed.Equalizer.mem_of_closed _ _ x hc ((mem_iff_closed X k L u v hu hv x hc).mp hx)
  · apply Projection.ProjectionCoincidence.closed_subset T.hom
    intro x hx hc
    exact (mem_iff_closed X k L u v hu hv x hc).mpr (Closed.Equalizer.eq_of_mem _ _ x hx)

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DefinedPair
