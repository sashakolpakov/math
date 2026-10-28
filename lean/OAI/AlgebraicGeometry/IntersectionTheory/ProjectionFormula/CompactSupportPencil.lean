import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ParameterGerms
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyIs

/-! # Compact Support Pencil -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompactSupportPencil

noncomputable section

/-! Every horizontal integral support of the actual compact family
ambient defines a proper rational pencil on the original source. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (C : IrreducibleCloseds (Projective.FamilyIs.FamilyCompactAmbient.space X))

def source : CycleClass.Geometric.GenericPoint.reducedSupportScheme C ⟶ X.carrier :=
  CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ Projective.FamilyIs.FamilyCompactAmbient.first X

def parameter : CycleClass.Geometric.GenericPoint.reducedSupportScheme C ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace 1 :=
  CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ Projective.FamilyIs.FamilyCompactAmbient.second X

instance proper : IsProper (source X C) := by
  unfold source
  infer_instance

instance noetherian : IsNoetherian (CycleClass.Geometric.GenericPoint.reducedSupportScheme C) where
  __ := LocallyOfFiniteType.isLocallyNoetherian (source X C)
  __ := QuasiCompact.compactSpace_of_compactSpace (source X C)

theorem over_base : parameter X C ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1 = source X C ≫ X.structureMap := by
  change (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ pullback.snd X.structureMap (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)) ≫ _ =
    (CycleClass.Geometric.GenericPoint.reducedSupportι C ≫ pullback.fst X.structureMap (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase 1)) ≫ _
  rw [Category.assoc, Category.assoc, pullback.condition]

theorem rationallyEquivalent
    (hη : parameter X C (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme C)) = genericPoint (Foundations.Scheme.ProjectiveSpace.projectiveSpace 1))
    (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (source X C ≫ X.structureMap) + p = m + 1) (a b : ℂ) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p
      (NormalizedRationalPencil.Proper.fiber X (source X C) p
        (Projective.LineParameter.pullback (parameter X C) hη) a)
      (NormalizedRationalPencil.Proper.fiber X (source X C) p
        (Projective.LineParameter.pullback (parameter X C) hη) b) :=
  Projective.ParameterGerms.Pencil.rationallyEquivalent (parameter X C) hη X (source X C)
    (over_base X C) m p hd a b

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompactSupportPencil
