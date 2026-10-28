import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.SupportClosure
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Open.PositiveParameterFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompactSupportPencil

/-! # Compact Family Component -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompactFamilyComponent

noncomputable section

/-! The closure of an actual integral family component in X × P¹
gives a proper pencil. Every good matrix parameter is covered by the
original open component, so its native endpoint fibers are equivalent. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Family

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)
  (D : IrreducibleCloseds (Projective.FamilyOnSource.Family.space X A))

def support : IrreducibleCloseds (Projective.FamilyIs.FamilyCompactAmbient.space X) :=
  Open.SupportClosure.closure (Projective.FamilyIs.FamilyCompactAmbient.inclusion X A) D

def map : CycleClass.Geometric.GenericPoint.reducedSupportScheme D ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme (support X A D) :=
  Open.SupportClosure.map (Projective.FamilyIs.FamilyCompactAmbient.inclusion X A) D

instance map_open : IsOpenImmersion (Family.map X A D) :=
  inferInstanceAs (IsOpenImmersion
    (Open.SupportClosure.map (Projective.FamilyIs.FamilyCompactAmbient.inclusion X A) D))

theorem map_source : Family.map X A D ≫ CompactSupportPencil.source X (support X A D) =
    CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ Projective.FamilyOnSource.Family.toSource X A := by
  change Open.SupportClosure.map (Projective.FamilyIs.FamilyCompactAmbient.inclusion X A) D ≫
    (CycleClass.Geometric.GenericPoint.reducedSupportι (support X A D) ≫ Projective.FamilyIs.FamilyCompactAmbient.first X) = _
  dsimp only [support]
  rw [← Category.assoc, Open.SupportClosure.map_fac, Category.assoc,
    Projective.FamilyIs.FamilyCompactAmbient.inclusion_first]

theorem map_parameter : Family.map X A D ≫ CompactSupportPencil.parameter X (support X A D) =
    (CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ Projective.FamilySections.Family.parameter X A) ≫
      Projective.FamilyIs.MatrixParameterOpen.inclusion A := by
  change Open.SupportClosure.map (Projective.FamilyIs.FamilyCompactAmbient.inclusion X A) D ≫
    (CycleClass.Geometric.GenericPoint.reducedSupportι (support X A D) ≫ Projective.FamilyIs.FamilyCompactAmbient.second X) = _
  dsimp only [support]
  rw [← Category.assoc, Open.SupportClosure.map_fac, Category.assoc,
    Projective.FamilyIs.FamilyCompactAmbient.inclusion_second, Category.assoc]

theorem horizontal
    (hη : ((CycleClass.Geometric.GenericPoint.reducedSupportι D ≫ Projective.FamilySections.Family.parameter X A) ≫
      Projective.FamilyIs.MatrixParameterOpen.inclusion A) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) =
        genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1)) :
    CompactSupportPencil.parameter X (support X A D)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (support X A D))) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1) := by
  rw [← genericPoint_eq_of_isOpenImmersion (Family.map X A D)]
  change (Family.map X A D ≫ CompactSupportPencil.parameter X (support X A D))
    (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme D)) = _
  rw [map_parameter]
  exact hη

theorem good_point (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0) :
    Projective.ParameterFiber.point a ∈ Set.range (Projective.FamilyIs.MatrixParameterOpen.inclusion A) := by
  refine ⟨(Spec.map (CommRingCat.ofHom (Polynomial.MatrixPath.evaluation A a ha)))
    (IsLocalRing.closedPoint ℂ), ?_⟩
  have he := congrArg (fun f : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1 => f (IsLocalRing.closedPoint ℂ))
    (Projective.FamilyIs.MatrixParameterOpen.evaluation A a ha)
  exact he.trans (congrArg Projective.FamilyIs.MatrixParameterOpen.affine (Affine.ParameterFiber.point_spec ℂ a))

theorem covers (a : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme (support X A D))
    (hz : CompactSupportPencil.parameter X (support X A D) z = Projective.ParameterFiber.point a) :
    z ∈ Set.range (Family.map X A D) :=
  Open.SupportClosure.Pullback.covers (Projective.FamilyIs.FamilyCompactAmbient.inclusion X A)
    (Projective.FamilySections.Family.parameter X A) (Projective.FamilyIs.FamilyCompactAmbient.second X)
    (Projective.FamilyIs.MatrixParameterOpen.inclusion A) (Projective.FamilyIs.FamilyCompactAmbient.isPullback X A)
    D (Projective.ParameterFiber.point a) (good_point X A a ha) z hz

theorem dimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension D (Projective.FamilyOnSource.Family.toSource X A ≫ X.structureMap) =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
      (CompactSupportPencil.source X (support X A D) ≫ X.structureMap) := by
  have hd := Open.SupportClosure.dimension (Projective.FamilyIs.FamilyCompactAmbient.inclusion X A) D
    (Projective.FamilyIs.FamilyCompactAmbient.first X ≫ X.structureMap)
  rw [← Category.assoc, Projective.FamilyIs.FamilyCompactAmbient.inclusion_first] at hd
  exact hd

variable (hη : CompactSupportPencil.parameter X (support X A D)
  (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (support X A D))) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))

def fiber (p : ℕ) (a : ℂ) : X.RationalDimensionCycle p :=
  Open.PositiveParameterFiber.ProperPencil.fiber X (CompactSupportPencil.source X (support X A D))
    (Family.map X A D) (CompactSupportPencil.parameter X (support X A D)) hη p a

theorem rationallyEquivalent (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D
      (Projective.FamilyOnSource.Family.toSource X A ≫ X.structureMap) + p = m + 1)
    (a b : ℂ) (ha : (Polynomial.MatrixPath.determinant A).eval a ≠ 0)
    (hb : (Polynomial.MatrixPath.determinant A).eval b ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p (fiber X A D hη p a) (fiber X A D hη p b) := by
  rw [dimension] at hd
  exact Open.PositiveParameterFiber.ProperPencil.rationallyEquivalent X
    (CompactSupportPencil.source X (support X A D)) (Family.map X A D)
    (CompactSupportPencil.parameter X (support X A D)) hη
    (CompactSupportPencil.over_base X (support X A D)) m p hd a b
    (covers X A D a ha) (covers X A D b hb)

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompactFamilyComponent
