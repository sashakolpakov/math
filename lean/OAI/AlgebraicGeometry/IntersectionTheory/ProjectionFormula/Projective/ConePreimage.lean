import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.PointIdeal

/-! # Cone Preimage -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConePreimage

noncomputable section

/-! The constructed projective cone pulls back on a center-free
subscheme to the actual inverse image of the projected support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport

theorem mem_iff {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) (η : Foundations.Scheme.ProjectiveSpace.projectiveSpace m)
    {S : Scheme} (i : S ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n)
    (hi : ∀ x, i x ∈ BasicOpen.RationalProjection.domain (ConeSupport.coordinates L)) (x : S) :
    i x ∈ ConeSupport.support L hL η ↔ ProjectionRestriction.projection (ConeSupport.coordinates L) i hi x ∈
      (irreducibleSetEquivPoints.symm η : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace m)) := by
  rw [ConeSupport.mem_support]
  have hmap := Projection.PointIdeal.ideal (ConeSupport.coordinates L) i hi
    (HomogeneousCoordinateMap.ofForms_C _ _) x
  have he : ProjectionRestriction.projection (ConeSupport.coordinates L) i hi x ∈
      (irreducibleSetEquivPoints.symm η : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace m)) ↔
      η.asHomogeneousIdeal ≤
        (ProjectionRestriction.projection (ConeSupport.coordinates L) i hi x).asHomogeneousIdeal :=
    (ProjectiveSpectrum.le_iff_mem_closure (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) η _).symm
  rw [he, hmap]
  exact Ideal.map_le_iff_le_comap

theorem finite_image {S : Scheme} {m : ℕ} (f : S ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m) [IsProper f]
    (W : IrreducibleCloseds S) :
    (irreducibleSetEquivPoints.symm (f (CycleClass.Thom.IntersectionGeometry.supportPoint W)) : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace m)) = f '' (W : Set S) := by
  change closure {f (CycleClass.Thom.IntersectionGeometry.supportPoint W)} = _
  have h := f.isClosedMap.closure_image_eq_of_continuous f.continuous {CycleClass.Thom.IntersectionGeometry.supportPoint W}
  rw [Set.image_singleton] at h
  have hW : closure {CycleClass.Thom.IntersectionGeometry.supportPoint W} = (W : Set S) :=
    congrArg (fun C : IrreducibleCloseds S => (C : Set S)) (irreducibleSetEquivPoints.symm_apply_apply W)
  rw [hW] at h
  exact h

theorem intersection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
    (hL : LinearIndependent ℂ L)
    (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
    (W : IrreducibleCloseds X.carrier) :
    X.embedding ⁻¹' (ConeSupport.support L hL (Projection.FiniteProjective.FromForms.map X m L h (CycleClass.Thom.IntersectionGeometry.supportPoint W)) : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) =
      Projection.FiniteProjective.FromForms.map X m L h ⁻¹' (Projection.FiniteProjective.FromForms.map X m L h '' (W : Set X.carrier)) := by
  have he := finite_image (Projection.FiniteProjective.FromForms.map X m L h) W
  ext x
  have hm := mem_iff L hL (Projection.FiniteProjective.FromForms.map X m L h (CycleClass.Thom.IntersectionGeometry.supportPoint W)) X.embedding
    (Projection.FiniteProjective.FromForms.in_domain X m L h) x
  exact hm.trans ((congrArg (fun A : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace m) => Projection.FiniteProjective.FromForms.map X m L h x ∈ A) he).to_iff)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConePreimage
