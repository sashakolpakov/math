import OAI.AlgebraicGeometry.Cycles.Functoriality.DimensionPreserving
import OAI.AlgebraicGeometry.Cycles.Functoriality.SupportClass
import OAI.AlgebraicGeometry.Cycles.Functoriality.BirationalDegree

/-! # Resolution -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.Resolution.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem fullCycleSupport_genericPoint (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (Support.Construction.fullCycleSupport V).genericPoint = genericPoint V.carrier :=
  (Support.Construction.fullCycleSupport V).genericPoint_spec.eq (genericPoint_spec V.carrier)

/-- The image of the full resolution source is the specified irreducible support. -/
theorem resolves_imageSupport
    {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (g : R.toOver ⟶ X.toOver) (hres : UnitCap.Resolves g Z) :
    UnitCap.imageSupport g (Support.Construction.fullCycleSupport R) = Z.1 := by
  apply irreducibleSetEquivPoints.injective
  change irreducibleSetEquivPoints (irreducibleSetEquivPoints.symm
    (g.left (Support.Construction.fullCycleSupport R).genericPoint)) = Z.genericPoint
  let e : IrreducibleCloseds X.carrier ≃o X.carrier := irreducibleSetEquivPoints
  exact (e.apply_symm_apply (SupportMap.Construction.algebraicMap g (Support.Construction.fullCycleSupport R).genericPoint)).trans
    ((congrArg (SupportMap.Construction.algebraicMap g) (fullCycleSupport_genericPoint R)).trans
      (BirationalDegree.Construction.resolves_genericPoint Z g hres))

theorem resolves_supportDimension
    {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (g : R.toOver ⟶ X.toOver) (hres : UnitCap.Resolves g Z)
    (hdeg : 0 + X.complexDimension = p + R.complexDimension) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (UnitCap.imageSupport g (Support.Construction.fullCycleSupport R)) X.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Support.Construction.fullCycleSupport R).1 R.structureMap := by
  rw [resolves_imageSupport Z g hres]
  have hZ := Z.dimension_add_codimension
  have hR := (Support.Construction.fullCycleSupport R).dimension_add_codimension
  rw [← X.complexDimension_eq_transcendenceDimension] at hZ
  rw [← R.complexDimension_eq_transcendenceDimension] at hR
  omega

/-- Algebraic pushforward of the resolution source's full cycle is the
specified support with coefficient one. -/
theorem resolves_pushforward_fullCycle
    {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (g : R.toOver ⟶ X.toOver) (hres : UnitCap.Resolves g Z)
    (hdeg : 0 + X.complexDimension = p + R.complexDimension) :
    UnitCap.cyclePushforwardGenerator g 0 p hdeg (Support.Construction.fullCycleSupport R) = Finsupp.single Z 1 := by
  have hdim := resolves_supportDimension Z g hres hdeg
  have hT : (⟨UnitCap.imageSupport g (Support.Construction.fullCycleSupport R),
      UnitCap.imageCodimension_eq g 0 p hdeg (Support.Construction.fullCycleSupport R) hdim⟩ : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) = Z :=
    Subtype.ext (resolves_imageSupport Z g hres)
  rw [UnitCap.cyclePushforwardGenerator_of_dimension_eq g 0 p hdeg (Support.Construction.fullCycleSupport R) hdim,
    hT, fullCycleSupport_genericPoint, BirationalDegree.Construction.resolves_residueDegree Z g hres, Nat.cast_one]

/-- The geometric class of an irreducible support is the proper
cohomological pushforward of the unit on any smooth proper birational resolution. -/
theorem cycleClass_of_resolution
    {R X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p)
    (g : R.toOver ⟶ X.toOver) (hg : IsProper g.left)
    (hres : UnitCap.Resolves g Z)
    (hdeg : 0 + X.complexDimension = p + R.complexDimension) :
    Z.geometricCycleClass =
      UnitCap.cohomologyPushforward g hg 0 p hdeg (UnitCap.cohomologyUnit R) := by
  have h := DimensionPreserving.Construction.cycleClass_proper_pushforward g hg 0 p hdeg (Finsupp.single (Support.Construction.fullCycleSupport R) 1)
  rw [UnitCap.cyclePushforward_single, one_smul, resolves_pushforward_fullCycle Z g hres hdeg,
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single,
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single, one_smul, one_smul,
    SupportClass.Construction.fullCycleSupport_geometricCycleClass] at h
  exact h

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.Resolution.Construction
