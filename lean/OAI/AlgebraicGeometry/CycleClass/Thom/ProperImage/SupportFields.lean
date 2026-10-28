import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.SupportMap
import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.FunctionFields

/-! # Support Fields -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.SupportFields.Constructions.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem imageSupport_dimension_le {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport X p) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap ≤
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap := by
  let i := SupportMap.Constructions.Construction.supportImageMap f hf Z
  let g := Geometric.SupportFiniteType.supportStructureMap (Reduction.Constructions.imageSupport f Z) Y.structureMap
  let : LocallyOfFiniteType (i ≫ g) := by
    change LocallyOfFiniteType (SupportMap.Constructions.Construction.supportImageMap f hf Z ≫
      Geometric.SupportFiniteType.supportStructureMap (Reduction.Constructions.imageSupport f Z) Y.structureMap)
    rw [SupportMap.Constructions.Construction.supportImageMap_over]
    infer_instance
  have h := FunctionFields.Constructions.Construction.dimension_le_of_genericPoint i (SupportMap.Constructions.Construction.supportImageMap_genericPoint f hf Z) g
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Z.structureMap
  rw [← SupportMap.Constructions.Construction.supportImageMap_over f hf Z]
  exact h

/-- The zero branch of algebraic pushforward is genuinely dimension drop. -/
theorem imageSupport_dimension_lt_of_ne {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (h : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap ≠
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap <
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap :=
  lt_of_le_of_ne (imageSupport_dimension_le f hf Z) h

/-- The induced embedding of the two supports' actual function fields. -/
def supportFunctionFieldMap {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport X p) :
    (Geometric.GenericPoint.reducedSupportScheme (Reduction.Constructions.imageSupport f Z)).functionField ⟶ Z.scheme.functionField :=
  FunctionFields.Constructions.Construction.genericFieldMap (SupportMap.Constructions.Construction.supportImageMap f hf Z) (SupportMap.Constructions.Construction.supportImageMap_genericPoint f hf Z)

/-- For a dimension-preserving support, the function-field extension
underlying its algebraic pushforward has finite degree. -/
theorem supportFunctionField_finite {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (hf : IsProper f.left)
    {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport X p)
    (hdim : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Reduction.Constructions.imageSupport f Z) Y.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 X.structureMap) :
    letI := (supportFunctionFieldMap f hf Z).hom.toAlgebra
    Module.Finite (Geometric.GenericPoint.reducedSupportScheme (Reduction.Constructions.imageSupport f Z)).functionField
      Z.scheme.functionField := by
  let i := SupportMap.Constructions.Construction.supportImageMap f hf Z
  let g := Geometric.SupportFiniteType.supportStructureMap (Reduction.Constructions.imageSupport f Z) Y.structureMap
  let : LocallyOfFiniteType (i ≫ g) := by
    change LocallyOfFiniteType (SupportMap.Constructions.Construction.supportImageMap f hf Z ≫
      Geometric.SupportFiniteType.supportStructureMap (Reduction.Constructions.imageSupport f Z) Y.structureMap)
    rw [SupportMap.Constructions.Construction.supportImageMap_over]
    infer_instance
  apply FunctionFields.Constructions.Construction.genericField_extension_finite i (SupportMap.Constructions.Construction.supportImageMap_genericPoint f hf Z) g
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
    (SupportMap.Constructions.Construction.supportImageMap f hf Z ≫ Geometric.SupportFiniteType.supportStructureMap (Reduction.Constructions.imageSupport f Z) Y.structureMap)
  rw [SupportMap.Constructions.Construction.supportImageMap_over]
  exact hdim

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.SupportFields.Constructions.Construction
