import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Generic

/-! # Projection Coincidence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ProjectionCoincidence

noncomputable section

section

/-! The partial projection agrees with the finite projection when the
chosen coordinates have no common zero. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Restriction

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)

include h in
theorem domain_top : PartialLinear.Projection.domain X m L = ⊤ := by
  apply top_unique
  intro x _
  exact (PartialLinear.Projection.mem_domain X m L x).mpr (h x)

theorem map_eq : PartialLinear.Projection.map X m L =
    (PartialLinear.Projection.domain X m L).ι ≫ FiniteProjective.FromForms.map X m L h := by
  unfold PartialLinear.Projection.map FiniteProjective.FromForms.map
    Projective.ProjectionRestriction.projection
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono (Projective.BasicOpen.RationalProjection.domain
    (FiniteProjective.FromForms.coordinates X m L)).ι).mp
  rw [Projective.ProjectionRestriction.lift_fac, Category.assoc,
    Projective.ProjectionRestriction.lift_fac]

variable {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (u v : T ⟶ X.toOver)

include h in
theorem pair_domain_top : Coincidence.domain X m L u v = ⊤ := by
  apply top_unique
  intro x _
  exact ⟨(PartialLinear.Projection.mem_domain X m L (u.left x)).mpr (h (u.left x)),
    (PartialLinear.Projection.mem_domain X m L (v.left x)).mpr (h (v.left x))⟩

theorem first_eq : (Coincidence.first X m L u v).left =
    (Coincidence.domain X m L u v).ι ≫ u.left ≫ FiniteProjective.FromForms.map X m L h := by
  change u.left.resLE _ _ _ ≫ PartialLinear.Projection.map X m L = _
  rw [map_eq X m L h, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

theorem second_eq : (Coincidence.second X m L u v).left =
    (Coincidence.domain X m L u v).ι ≫ v.left ≫ FiniteProjective.FromForms.map X m L h := by
  change v.left.resLE _ _ _ ≫ PartialLinear.Projection.map X m L = _
  rw [map_eq X m L h, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

end Restriction

end

/-! The closed coincidence locus of a complete projection is the
actual scheme equalizer on the scheme of pairs. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem closed_subset {S : Scheme} (f : S ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (A B : Closeds S) (h : ∀ x ∈ A, IsClosed ({x} : Set S) → x ∈ B) : A ≤ B := by
  let : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace f
  have he : closure ((A : Set S) ∩ closedPoints S) = (A : Set S) :=
    (JacobsonSpace.closure_inter_closedPoints_eq_closure A.isClosed.isLocallyClosed).trans A.isClosed.closure_eq
  change (A : Set S) ⊆ B
  rw [← he]
  exact closure_minimal (fun x hx => h x hx.1 hx.2) B.isClosed

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)

def over : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) :=
  Over.homMk (FiniteProjective.FromForms.map X m L h) (FiniteProjective.FromForms.over_base X m L h)

variable {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (u v : T ⟶ X.toOver) [LocallyOfFiniteType T.hom]

theorem mem_iff_closed (x : T.left) (hx : IsClosed ({x} : Set T.left)) :
    x ∈ Coincidence.locus X m L u v ↔
      FiniteProjective.FromForms.map X m L h (u.left x) =
        FiniteProjective.FromForms.map X m L h (v.left x) := by
  let U := Coincidence.domain X m L u v
  let y : U := ⟨x, by
    change x ∈ Coincidence.domain X m L u v
    rw [Restriction.pair_domain_top X m L h u v]
    trivial⟩
  have hset : U.ι ⁻¹' ({x} : Set T.left) = ({y} : Set (U : Scheme)) := by
    ext z
    change z.val = x ↔ z = y
    constructor
    · exact fun hz => Subtype.ext hz
    · rintro rfl
      rfl
  have hy : IsClosed ({y} : Set (U : Scheme)) := hset ▸ hx.preimage U.ι.continuous
  have he := Coincidence.mem_iff_closed X m L u v y hy
  rw [Restriction.first_eq X m L h u v,
    Restriction.second_eq X m L h u v] at he
  exact he

theorem locus_eq : Coincidence.locus X m L u v =
    Closed.Equalizer.locus (u ≫ over X m L h) (v ≫ over X m L h) := by
  apply le_antisymm
  · apply closed_subset T.hom
    intro x hx hc
    exact Closed.Equalizer.mem_of_closed _ _ x hc ((mem_iff_closed X m L h u v x hc).mp hx)
  · apply closed_subset T.hom
    intro x hx hc
    exact (mem_iff_closed X m L h u v x hc).mpr (Closed.Equalizer.eq_of_mem _ _ x hx)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ProjectionCoincidence
