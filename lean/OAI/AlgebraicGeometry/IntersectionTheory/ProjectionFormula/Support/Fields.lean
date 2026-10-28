import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map
import OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields
import Mathlib.RingTheory.Norm.Basic

/-! # Fields -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields

noncomputable section

/-! Actual function fields and norms for the support-to-image morphism.
Equal support dimensions imply finiteness; no finiteness assertion is
assumed as a field on the morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map OAI.AlgebraicGeometry.Cycles.Functoriality.FunctionFields.Construction

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}

def supportFunctionFieldMap (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W)).functionField ⟶
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (Map.supportImageMap f W) (Map.supportImageMap_genericPoint f W)

theorem image_dimension_le (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap := by
  have h := Cycles.Functoriality.FunctionFields.Construction.dimension_le_of_genericPoint (Map.supportImageMap f W)
    (Map.supportImageMap_genericPoint f W)
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap)
  rw [Map.supportImageMap_over] at h
  exact h

theorem supportFunctionField_finite (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap) :
    letI := (supportFunctionFieldMap f W).hom.toAlgebra
    Module.Finite (CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W)).functionField
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField := by
  apply Cycles.Functoriality.FunctionFields.Construction.genericField_extension_finite (Map.supportImageMap f W)
    (Map.supportImageMap_genericPoint f W)
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ProperCycleLinearity.imageSupport f W) Y.structureMap)
  rw [Map.supportImageMap_over]
  exact hdim

def functionFieldResidueIso (S : Scheme) [IsIntegral S] :
    S.functionField ≅ S.residueField (genericPoint S) :=
  (RingEquiv.ofBijective (S.residue (genericPoint S)).hom
    ⟨(show S.functionField →+* S.residueField (genericPoint S) from
      (S.residue (genericPoint S)).hom).injective,
      S.residue_surjective (genericPoint S)⟩).toCommRingCatIso

theorem genericFieldMap_residue_square {S T : Scheme} [IsIntegral S] [IsIntegral T]
    (i : S ⟶ T) (hη : i (genericPoint S) = genericPoint T) :
    (functionFieldResidueIso T).hom ≫ (T.residueFieldCongr hη.symm).hom ≫
        i.residueFieldMap (genericPoint S) =
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη ≫ (functionFieldResidueIso S).hom := by
  change T.residue (genericPoint T) ≫ (T.residueFieldCongr hη.symm).hom ≫
      i.residueFieldMap (genericPoint S) =
    (T.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom ≫
      i.stalkMap (genericPoint S) ≫ S.residue (genericPoint S)
  rw [← Category.assoc, Scheme.residue_residueFieldCongr,
    Category.assoc, Scheme.residue_residueFieldMap]

theorem genericFieldMap_finrank_eq_residueDegree {S T : Scheme}
    [IsIntegral S] [IsIntegral T] (i : S ⟶ T)
    (hη : i (genericPoint S) = genericPoint T) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη).hom.toAlgebra
    Module.finrank T.functionField S.functionField = i.residueDegree (genericPoint S) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap i hη).hom.toAlgebra
  let := (i.residueFieldMap (genericPoint S)).hom.toAlgebra
  apply Algebra.finrank_eq_of_equiv_equiv
    ((functionFieldResidueIso T) ≪≫ T.residueFieldCongr hη.symm).commRingCatIsoToRingEquiv
    (functionFieldResidueIso S).commRingCatIsoToRingEquiv
  exact congrArg CommRingCat.Hom.hom (genericFieldMap_residue_square i hη)

theorem supportFunctionField_finrank_eq (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier) :
    letI := (supportFunctionFieldMap f W).hom.toAlgebra
    Module.finrank (CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W)).functionField
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField = f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint W) :=
  (genericFieldMap_finrank_eq_residueDegree (Map.supportImageMap f W)
    (Map.supportImageMap_genericPoint f W)).trans (Map.supportImageMap_generic_residueDegree f W)

theorem residueDegree_pos_of_dimension_eq (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap) :
    0 < f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint W) := by
  let := (supportFunctionFieldMap f W).hom.toAlgebra
  let := supportFunctionField_finite f W hdim
  rw [← supportFunctionField_finrank_eq f W]
  exact Module.finrank_pos

/-- The genuine norm between the two support function fields. -/
def supportNorm (f : X.toOver ⟶ Y.toOver) (W : IrreducibleCloseds X.carrier)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField →*
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W)).functionField :=
  letI := (supportFunctionFieldMap f W).hom.toAlgebra
  letI := supportFunctionField_finite f W hdim
  Algebra.norm (CycleClass.Geometric.GenericPoint.reducedSupportScheme (ProperCycleLinearity.imageSupport f W)).functionField

theorem supportNorm_ne_zero (f : X.toOver ⟶ Y.toOver)
    (W : IrreducibleCloseds X.carrier)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ProperCycleLinearity.imageSupport f W) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap)
    (a : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (ha : a ≠ 0) :
    supportNorm f W hdim a ≠ 0 := by
  let := (supportFunctionFieldMap f W).hom.toAlgebra
  let := supportFunctionField_finite f W hdim
  exact Algebra.norm_ne_zero_iff.mpr ha

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Fields
