import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFiberDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceEndpointFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading

/-! # Horizontal Family Grading -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyGrading

noncomputable section

/-! Only components of the matching dimension can contribute to
a graded endpoint cycle. Consequently every horizontal component
has equivalent good fibers in every codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))
  (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ CompactHorizontalFamilyFiber.Family.parameter X A) ≫ Projective.FamilyIs.MatrixParameterOpen.affine)
    (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

theorem point_dimension (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (y : Projective.FamilyOnSource.Family.space X A)
    (hy : HorizontalFamilyFiber.Family.cycle (Projective.FamilyOnSource.Family.space X A) D
      (CompactHorizontalFamilyFiber.Family.parameter X A) hη a y ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension
      (irreducibleSetEquivPoints.symm (Projective.FamilyOnSource.Family.toSource X A y)) X.structureMap + 1 =
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (Projective.FamilyOnSource.Family.toSource X A ≫ X.structureMap) := by
  let : LocallyOfFiniteType (Projective.FamilyOnSource.Family.toSource X A ≫ X.structureMap) := by
    rw [← Projective.FamilyIs.FamilyCompactAmbient.inclusion_first X A, Category.assoc]
    infer_instance
  have hd := HorizontalFiberDimension.dimension (Projective.FamilyOnSource.Family.space X A) D
    (CompactHorizontalFamilyFiber.Family.parameter X A) hη
    (Projective.FamilyOnSource.Family.toSource X A ≫ X.structureMap) a y hy
  have ht := HorizontalFiberDimension.parameter (Projective.FamilyOnSource.Family.space X A) D
    (CompactHorizontalFamilyFiber.Family.parameter X A) hη a y hy
  let := Projective.FamilySections.Family.source_closed X A a ha
  have he := Closed.PointClosureDimension.retraction
    (Projective.FamilyOnSource.Family.specialization X A a ha) (Projective.FamilyOnSource.Family.toSource X A)
    (Projective.FamilyOnSource.Family.specialization_source X A a ha) X.structureMap
    (Projective.FamilyOnSource.Family.toSource X A y)
  rw [SourceEndpointFiber.point X A a ha y ht] at he
  rw [he] at hd
  exact hd

theorem zero_of_dimension (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D
      (Projective.FamilyOnSource.Family.toSource X A ≫ X.structureMap) + p ≠ m + 1)
    (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0) :
    CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A)
      (HorizontalFamilyFiber.Family.cycle (Projective.FamilyOnSource.Family.space X A) D
        (CompactHorizontalFamilyFiber.Family.parameter X A) hη a)) = 0 := by
  ext B
  rw [Principal.ClosedSectionCycle.degreeComponent_apply, Finsupp.zero_apply]
  by_contra hn
  obtain ⟨y, hy, he⟩ := PointPushforwardSupport.exists_point
    (Projective.FamilyOnSource.Family.toSource X A) _ (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) hn
  have hdim := point_dimension X A D hη a ha y hy
  rw [he, show irreducibleSetEquivPoints.symm (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) = B.val from
    irreducibleSetEquivPoints.symm_apply_apply B.val] at hdim
  have hB := Grading.supportDimension_add_codimension X m B.val
  rw [B.property] at hB
  apply hd
  omega

theorem rationallyEquivalent (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p
      (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A)
        (HorizontalFamilyFiber.Family.cycle (Projective.FamilyOnSource.Family.space X A) D
          (CompactHorizontalFamilyFiber.Family.parameter X A) hη a)))
      (CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (Projective.FamilyOnSource.Family.toSource X A)
        (HorizontalFamilyFiber.Family.cycle (Projective.FamilyOnSource.Family.space X A) D
          (CompactHorizontalFamilyFiber.Family.parameter X A) hη b))) := by
  by_cases hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D
      (Projective.FamilyOnSource.Family.toSource X A ≫ X.structureMap) + p = m + 1
  · exact CompactHorizontalFamilyFiber.Family.rationallyEquivalent X A D hη m p hd a b ha hb
  · rw [zero_of_dimension X A D hη m p hd a ha, zero_of_dimension X A D hη m p hd b hb]
    exact CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X p 0

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HorizontalFamilyGrading
