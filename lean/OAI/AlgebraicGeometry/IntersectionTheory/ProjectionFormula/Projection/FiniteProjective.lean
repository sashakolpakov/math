import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearCut
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousCoordinateMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.Finite

/-! # Finite Projective -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiniteProjective

noncomputable section

section

/-! Every smooth projective m-dimensional presentation admits an
actual finite linear projection to projective m-space, constructed from
m+1 homogeneous linear forms with no common zero on the presentation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem exists_coordinates (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    ∃ f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension,
      (∀ z : ℂ, f (MvPolynomial.C z) = MvPolynomial.C z) ∧
      ∀ x : X.carrier, X.embedding x ∈ Projective.BasicOpen.RationalProjection.domain f := by
  obtain ⟨L, hL, hav⟩ := Projective.LinearCut.exists_no_common_zero X m
  refine ⟨HomogeneousCoordinateMap.ofForms L hL, HomogeneousCoordinateMap.ofForms_C L hL, ?_⟩
  intro x
  obtain ⟨j, hj⟩ := hav x
  apply Opens.mem_iSup.mpr
  refine ⟨j, ?_⟩
  change HomogeneousCoordinateMap.ofForms L hL (MvPolynomial.X j) ∉
    (X.embedding x).asHomogeneousIdeal
  rwa [HomogeneousCoordinateMap.ofForms_X]

theorem exists_finite_projection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    ∃ π : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m,
      π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap ∧ IsFinite π := by
  obtain ⟨f, hC, hav⟩ := exists_coordinates X m
  refine ⟨Projective.ProjectionRestriction.projection f X.embedding hav, ?_,
    Projective.Finite.Projection.isFinite f X.embedding hav hC⟩
  rw [Projective.ProjectionRestriction.over_base f X.embedding hav hC, X.embedding_over]

end

/-! The finite projection associated to a specified tuple of
homogeneous linear forms with no common zero. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace FromForms

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)

def coordinates : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension :=
  HomogeneousCoordinateMap.ofForms (fun a => (L a).val) (fun a => (L a).property)

theorem constants (c : ℂ) : coordinates X m L (MvPolynomial.C c) = MvPolynomial.C c :=
  HomogeneousCoordinateMap.ofForms_C _ _ c

theorem coordinate (a : Fin (m + 1)) : coordinates X m L (MvPolynomial.X a) = (L a).val :=
  HomogeneousCoordinateMap.ofForms_X _ _ a

include h in
theorem in_domain (x : X.carrier) : X.embedding x ∈ Projective.BasicOpen.RationalProjection.domain (coordinates X m L) := by
  obtain ⟨a, ha⟩ := h x
  apply Opens.mem_iSup.mpr
  refine ⟨a, ?_⟩
  change coordinates X m L (MvPolynomial.X a) ∉ (X.embedding x).asHomogeneousIdeal
  rwa [coordinate]

def map : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m :=
  Projective.ProjectionRestriction.projection (coordinates X m L) X.embedding (in_domain X m L h)

theorem over_base : map X m L h ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap := by
  rw [map, Projective.ProjectionRestriction.over_base _ _ _ (constants X m L), X.embedding_over]

instance finite : IsFinite (map X m L h) :=
  Projective.Finite.Projection.isFinite _ _ _ (constants X m L)

end FromForms

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiniteProjective
