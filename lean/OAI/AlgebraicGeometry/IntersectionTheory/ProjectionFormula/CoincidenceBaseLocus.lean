import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoincidenceExtension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.CoordinateExtension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoincidenceClosedPointTest

/-! # Coincidence Base Locus -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoincidenceBaseLocus

noncomputable section

/-! Adding a coordinate can create new coincidence only where both
points belonged to the old base locus. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Coincidence

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (k : ℕ)
  (L : Fin (k + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (u v : T ⟶ X.toOver)

def bothBase : Closeds T.left :=
  ⟨(u.left ⁻¹ᵁ PartialLinear.Projection.domain X k L : Set T.left)ᶜ ∩
    (v.left ⁻¹ᵁ PartialLinear.Projection.domain X k L : Set T.left)ᶜ,
    (u.left ⁻¹ᵁ PartialLinear.Projection.domain X k L).isOpen.isClosed_compl.inter
      (v.left ⁻¹ᵁ PartialLinear.Projection.domain X k L).isOpen.isClosed_compl⟩

theorem map_finiteType [LocallyOfFiniteType T.hom] : LocallyOfFiniteType u.left := by
  have hc : LocallyOfFiniteType (u.left ≫ X.structureMap) := by
    change LocallyOfFiniteType (u.left ≫ X.toOver.hom)
    rw [u.w]
    infer_instance
  let := hc
  exact locallyOfFiniteType_of_comp u.left X.structureMap

theorem subset [LocallyOfFiniteType T.hom] (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) :
    (Projection.Coincidence.locus X (k + 1) (Fin.cons a L) u v : Set T.left) ⊆
      Projection.Coincidence.locus X k L u v ⊔ bothBase X k L u v := by
  let U := Projection.Coincidence.domain X (k + 1) (Fin.cons a L) u v
  let : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
  let : JacobsonSpace X.carrier := LocallyOfFiniteType.jacobsonSpace X.structureMap
  let : JacobsonSpace X.toOver.left := inferInstanceAs (JacobsonSpace X.carrier)
  let : LocallyOfFiniteType u.left := map_finiteType X u
  let : LocallyOfFiniteType v.left := map_finiteType X v
  refine CoincidenceClosedPointTest.subset U
    (Projection.Coincidence.first X (k + 1) (Fin.cons a L) u v) (Projection.Coincidence.second X (k + 1) (Fin.cons a L) u v)
    (Projection.Coincidence.locus X k L u v ⊔ bothBase X k L u v) ?_
  intro x hx hmem
  have he := Closed.Equalizer.eq_of_mem
    (Projection.Coincidence.first X (k + 1) (Fin.cons a L) u v) (Projection.Coincidence.second X (k + 1) (Fin.cons a L) u v) x hmem
  rw [CoincidenceExtension.first_value, CoincidenceExtension.second_value] at he
  have hstatus := Projection.CoordinateExtension.domain_status_iff X k L a
    ⟨u.left x.val, x.property.1⟩ ⟨v.left x.val, x.property.2⟩ he
  by_cases hxu : u.left x.val ∈ PartialLinear.Projection.domain X k L
  · have hxv := hstatus.mp hxu
    have hxc : IsClosed ({x.val} : Set T.left) := U.ι.closePoints_subset_preimage_closedPoints hx
    have huc : IsClosed ({u.left x.val} : Set X.carrier) :=
      (U.ι ≫ u.left).closePoints_subset_preimage_closedPoints hx
    have hvc : IsClosed ({v.left x.val} : Set X.carrier) :=
      (U.ι ≫ v.left).closePoints_subset_preimage_closedPoints hx
    have huc' : IsClosed ({(⟨u.left x.val, hxu⟩ : PartialLinear.Projection.domain X k L)} :
        Set ((PartialLinear.Projection.domain X k L) : Scheme)) :=
      Closed.FiberPoints.closed (PartialLinear.Projection.domain X k L).ι _ huc
    have hvc' : IsClosed ({(⟨v.left x.val, hxv⟩ : PartialLinear.Projection.domain X k L)} :
        Set ((PartialLinear.Projection.domain X k L) : Scheme)) :=
      Closed.FiberPoints.closed (PartialLinear.Projection.domain X k L).ι _ hvc
    have heold := Projection.CoordinateExtension.old_images_eq X k L a
      ⟨u.left x.val, hxu⟩ ⟨v.left x.val, hxv⟩ huc' hvc' he
    let y : Projection.Coincidence.domain X k L u v := ⟨x.val, hxu, hxv⟩
    have hyc : IsClosed ({y} : Set ((Projection.Coincidence.domain X k L u v) : Scheme)) :=
      Closed.FiberPoints.closed (Projection.Coincidence.domain X k L u v).ι y hxc
    apply Or.inl
    apply (Projection.Coincidence.mem_iff_closed X k L u v y hyc).mpr
    rw [CoincidenceExtension.first_value, CoincidenceExtension.second_value]
    exact heold
  · exact Or.inr ⟨hxu, fun h => hxu (hstatus.mpr h)⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoincidenceBaseLocus
