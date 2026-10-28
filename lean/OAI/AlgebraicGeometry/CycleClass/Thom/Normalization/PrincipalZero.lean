import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal

/-! # Principal Zero -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero.Constructions.BoundaryUnion

/-! A single actual algebraic closed exceptional set works for the entire
finite normalization divisor and has strictly higher ambient codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientPurity.Constructions
  Principal.Constructions NormalizationDivisor.Boundary.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)

local instance : Smooth (AmbientMap.Constructions.smoothNormalizationOver V W).hom := AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : Fintype (Principal.Constructions.DivisorPoint V W g hg) := Fintype.ofFinite _

def commonBoundary : Closeds V.carrier :=
  ⟨(AmbientPurity.Constructions.normalizationExceptionalClosed V W : Set V.carrier) ∪
      ⋃ z : Principal.Constructions.DivisorPoint V W g hg, (NormalizationDivisor.Boundary.Constructions.omittedBoundary V W ⟨z.val, z.property.1⟩ : Set V.carrier),
    (AmbientPurity.Constructions.normalizationExceptionalClosed V W).isClosed.union (isClosed_iUnion_of_finite fun z =>
      (NormalizationDivisor.Boundary.Constructions.omittedBoundary V W ⟨z.val, z.property.1⟩).isClosed)⟩

theorem commonBoundary_codimension (A : IrreducibleCloseds V.carrier)
    (hA : (A : Set V.carrier) ⊆ commonBoundary V W g hg) :
    Geometric.DimensionCycles.dimensionCodimension V W + 1 < Geometric.DimensionCycles.dimensionCodimension V A := by
  have hη := A.isIrreducible.isGenericPoint_genericPoint A.isClosed
  have hx := hA hη.mem
  rcases hx with hx | hx
  · have hsub : (A : Set V.carrier) ⊆ AmbientPurity.Constructions.normalizationExceptionalClosed V W := by
      rw [← hη.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hx) (AmbientPurity.Constructions.normalizationExceptionalClosed V W).isClosed
    have h := AmbientPurity.Constructions.normalizationExceptional_codimension V W A hsub
    omega
  · obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
    apply NormalizationDivisor.Boundary.Constructions.omittedBoundary_codimension V W ⟨z.val, z.property.1⟩ A
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hz) (NormalizationDivisor.Boundary.Constructions.omittedBoundary V W ⟨z.val, z.property.1⟩).isClosed

def commonOpen : Opens V.analyticSpace := ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (commonBoundary V W g hg)

theorem commonOpen_subset_ambient :
    (commonOpen V W g hg : Set V.analyticSpace) ⊆ ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen V.toOver (AmbientMap.Constructions.ambientOpen V W) := by
  intro x hx hbad
  exact hx (Or.inl hbad)

theorem commonOpen_subset_divisor (z : Principal.Constructions.DivisorPoint V W g hg) :
    (commonOpen V W g hg : Set V.analyticSpace) ⊆
      ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (NormalizationDivisor.Boundary.Constructions.omittedBoundary V W ⟨z.val, z.property.1⟩) := by
  intro x hx hbad
  exact hx (Or.inr (Set.mem_iUnion.mpr ⟨z, hbad⟩))

theorem commonOpen_cohomologyRestriction_isIso :
    IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCohomologyRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (commonOpen V W g hg : Set V.analyticSpace)
      ((Geometric.DimensionCycles.dimensionCodimension V W + 1) + (Geometric.DimensionCycles.dimensionCodimension V W + 1))) :=
  ProperImage.ClosedSupportPurity.Constructions.Construction.closedComplement_cohomologyRestriction_isIso V (commonBoundary V W g hg) (Geometric.DimensionCycles.dimensionCodimension V W + 1)
    (commonBoundary_codimension V W g hg)

end AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero.Constructions.BoundaryUnion

namespace AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero
section

/-! Every retained compact trace of the actual ambient normalized
principal cycle vanishes, by the original rational-function boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Trace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
  Principal.Constructions BoundaryUnion NormalizationDivisor.Trace.Constructions
  NormalizationDivisor.Boundary.Constructions.CompactSupport SchemeDivisor.Trace.Constructions.Class

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)

local instance : Smooth (AmbientMap.Constructions.smoothNormalizationOver V W).hom := AmbientMap.Constructions.smoothNormalization_smooth V W
local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AmbientMap.Constructions.smoothNormalizationOver V W)) := AmbientTopology.Constructions.smoothNormalization_metrizable V W
local instance : Fintype (Principal.Constructions.DivisorPoint V W g hg) := Fintype.ofFinite _

theorem normalizedPrincipalCycle_trace_zero
    (n : ℕ) (hp : 2 + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AmbientMap.Constructions.smoothNormalizationOver V W).hom)
    (hq : (Geometric.DimensionCycles.dimensionCodimension V W + 1) + (Geometric.DimensionCycles.dimensionCodimension V W + 1) + n = 2 * V.complexDimension)
    (L : Compacts V.analyticSpace) (hL : (L : Set V.analyticSpace) ⊆ BoundaryUnion.commonOpen V W g hg)
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ n) :
    Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ n b
      (HomologicalComplex.homologyMap
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ) n
        ((V.poincareDuality ((Geometric.DimensionCycles.dimensionCodimension V W + 1) + (Geometric.DimensionCycles.dimensionCodimension V W + 1)) n hq).hom
          (V.geometricCycleClassMap (Geometric.DimensionCycles.dimensionCodimension V W + 1) (Principal.Constructions.normalizedPrincipalCycle V W g hg)))) = 0 := by
  let S := AmbientMap.Constructions.smoothNormalizationOver V W
  let p := Geometric.DimensionCycles.dimensionCodimension V W + 1
  have hLO := hL.trans (BoundaryUnion.commonOpen_subset_ambient V W g hg)
  let bS := AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S))
    ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (L : Set V.analyticSpace), NormalizationDivisor.Boundary.Constructions.CompactSupport.fullAmbientMap_compactPreimage V W L hLO⟩ n
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (PrincipalBoundary.Constructions.fullAmbientMap V W))
      (A := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PrincipalBoundary.Constructions.fullAmbientMap V W) ⁻¹' (L : Set V.analyticSpace))ᶜ)
      (B := (L : Set V.analyticSpace)ᶜ) (fun _ hx => hx) n b)
  let sourceEval : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)) 2 →ₗ[ℚ] ℚ :=
    (LinearMap.applyₗ' ℚ bS).comp
      (AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) 2 n hp)
  let targetEval : V.rationalCohomology (p + p) →ₗ[ℚ] ℚ :=
    (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ n b).comp
      ((HomologicalComplex.homologyMap
        (Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ) n).hom.comp
        (V.poincareDuality (p + p) n hq).hom.hom)
  have hz := congrArg sourceEval (SchemeDivisor.Trace.Constructions.Class.principal_absolute_sum_zero S (PrincipalBoundary.Constructions.normalizedUnitRepresentative V W g hg)
    (PrincipalBoundary.Constructions.normalizedFunction_ne_zero V W g hg))
  simp only [map_sum, map_smul, map_zero] at hz
  have hterm (z : Principal.Constructions.DivisorPoint V W g hg) :
      sourceEval (SchemeDivisor.Trace.Constructions.Class.absoluteDivisorClass S ⟨z.val, z.property.1⟩) =
      ((PrincipalBoundary.Constructions.fullAmbientMap V W).left.residueDegree z.val : ℚ) •
        targetEval (NormalizationDivisor.Image.Constructions.imageCycleSupport V W ⟨z.val, z.property.1⟩).geometricCycleClass :=
    NormalizationDivisor.Trace.Constructions.normalization_divisor_compactTrace V W ⟨z.val, z.property.1⟩ n hp hq L hLO
      (hL.trans (BoundaryUnion.commonOpen_subset_divisor V W g hg z)) b
  change targetEval (V.geometricCycleClassMap p (Principal.Constructions.normalizedPrincipalCycle V W g hg)) = 0
  rw [Principal.Constructions.normalizedPrincipalCycle, map_sum, map_sum]
  refine Eq.trans (Finset.sum_congr rfl ?_) hz
  intro z _
  rw [map_smul, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single, map_smul, map_smul]
  exact congrArg (fun a => ((AmbientMap.Constructions.smoothNormalizationOver V W).left.ord (PrincipalBoundary.Constructions.normalizedFunction V W g) z.val : ℚ) • a)
    (hterm z).symm

end Constructions.Trace

end

/-! The exact principal cycle obtained from the actual normalization has
zero independently defined ambient geometric cohomology class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions.Class

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientTopology.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Principal.Constructions
  BoundaryUnion Trace

/-- The genuine relative cohomology tests detect a relative rational
homology class, by field universal coefficients and linear dual separation. -/
theorem relativeHomology_eq_zero_of_tests (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (a : Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ X A n)
    (ha : ∀ b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A n,
      Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n b a = 0) : a = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℚ a).mp
  intro f
  obtain ⟨b, rfl⟩ := (Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ X A n).surjective f
  exact ha b

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (W : IrreducibleCloseds V.carrier)
  (g : (Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)

local instance : Smooth (AmbientMap.Constructions.smoothNormalizationOver V W).hom := AmbientMap.Constructions.smoothNormalization_smooth V W

theorem normalizedPrincipalCycle_geometricClass_zero :
    V.geometricCycleClassMap (Geometric.DimensionCycles.dimensionCodimension V W + 1) (Principal.Constructions.normalizedPrincipalCycle V W g hg) = 0 := by
  let p := Geometric.DimensionCycles.dimensionCodimension V W + 1
  let a := V.geometricCycleClassMap p (Principal.Constructions.normalizedPrincipalCycle V W g hg)
  by_cases hp : p ≤ V.complexDimension
  · let n := 2 * (V.complexDimension - p)
    have hq : (p + p) + n = 2 * V.complexDimension := ProperImage.Reduction.Constructions.sourceComplementDegree V p hp
    have hs : 2 + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension (AmbientMap.Constructions.smoothNormalizationOver V W).hom := by
      have hd := AmbientTopology.Constructions.smoothNormalization_dimension V W
      rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension] at hd
      have hw := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension V W
      rw [← V.complexDimension_eq_transcendenceDimension] at hw
      dsimp only [p, n] at hp ⊢
      omega
    apply (V.poincareDuality (p + p) n hq).toLinearEquiv.injective
    change (V.poincareDuality (p + p) n hq).hom a = (V.poincareDuality (p + p) n hq).hom 0
    rw [map_zero]
    apply ProperImage.CompactProjection.Constructions.Construction.ordinaryHomology_eq_of_compactProjections_outside_closed V (BoundaryUnion.commonBoundary V W g hg) p n hq
      (BoundaryUnion.commonBoundary_codimension V W g hg) _ 0
    intro L hL
    rw [map_zero]
    apply relativeHomology_eq_zero_of_tests (TopCat.of V.analyticSpace) (L : Set V.analyticSpace)ᶜ n
    intro b
    exact Trace.normalizedPrincipalCycle_trace_zero V W g hg n hs hq L hL b
  · exact ProperImage.Reduction.Constructions.sourceCohomology_eq_zero V p (Nat.lt_of_not_ge hp) a

end Constructions.Class

end AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalZero

end

end OAI
