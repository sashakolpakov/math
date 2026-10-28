import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClassMeaning
import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTraceMeaning
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactRelativeTrace
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainD
import OAI.AlgebraicTopology.Duality.Poincare.CompactMeaning
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportOpen
import OAI.AlgebraicTopology.Duality.Poincare.CompactTraceEvaluation

/-! # Geometric Cycle Trace Characterization -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTraceCharacterization

noncomputable section

/-!
# The fundamental-cycle meaning of the geometric cycle class

The ambient homology class below is the actual singular cap product of the
geometric cohomology class with the ambient integral fundamental class.
Compact relative traces use the actual absolute-to-relative projection and
inverse excision on the complement of the singular boundary.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold TensorProduct ChangeOfRings

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace DimensionCycleSupport

variable {V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The actual compact-relative trace of an ambient rational homology class,
for a compact subset of the genuine regular ambient open set. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientHomologyTrace (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (K : Compacts Z.regularAmbientSpace) (n : ℕ) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V.analyticSpace)).homology n ⟶
      AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ (TopCat.of Z.regularAmbientSpace)
        (K : Set Z.regularAmbientSpace)ᶜ n :=
  Duality.Poincare.CompactFundamentalTrace.openCompactRelativeTrace (X := TopCat.of V.analyticSpace) Z.regularAmbientOpen K n

/-- The ambient geometric class capped with the constructed integral
fundamental class of the actual compact complex manifold. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleFundamentalClass (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V.analyticSpace)).homology
      (2 * Z.regularComplexDimension) :=
  Duality.Poincare.CompactMeaning.complexManifoldOrdinaryCap V.complexDimension (M := V.analyticSpace)
    (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
    Z.geometricCycleClass

/-- Every actual compact-relative trace is the proper trace of the regular
fundamental cycle. This predicate is the displayed family of homology equalities. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.HasRegularFundamentalCompactTraces (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V.analyticSpace)).homology
      (2 * Z.regularComplexDimension)) : Prop :=
  ∀ K : Compacts Z.regularAmbientSpace,
    Z.regularAmbientHomologyTrace K (2 * Z.regularComplexDimension) z =
      AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
        Z.isProperMap_regularComplementTopCatMap (K : Set Z.regularAmbientSpace)
        K.isCompact (2 * Z.regularComplexDimension)
        Z.regularRationalLocallyFiniteFundamentalClass

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleFundamentalClass_eq_cap (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.geometricCycleFundamentalClass =
      Duality.Poincare.MixedCapHomology.mixedSingularCapHomology (TopCat.of V.analyticSpace) (p + p)
        (2 * Z.regularComplexDimension) Z.geometricCycleClass
        (Duality.Poincare.CompactMeaning.complexFundamentalClassInDegree V.complexDimension (M := V.analyticSpace)
          ((p + p) + 2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree) :=
  rfl

/-- Testing the actual compact-relative trace of any ambient class's cap
is the canonical compact-support evaluation of its genuine restriction. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientHomologyTrace_cap_evaluation (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (K : Compacts Z.regularAmbientSpace) (a : V.rationalCohomology (p + p))
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (K : Set Z.regularAmbientSpace)ᶜ
      (2 * Z.regularComplexDimension)) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of Z.regularAmbientSpace)
        (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) b
        (Z.regularAmbientHomologyTrace K (2 * Z.regularComplexDimension)
          (Duality.Poincare.CompactMeaning.complexManifoldOrdinaryCap V.complexDimension (M := V.analyticSpace)
            (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree a)) =
      Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p) (2 * Z.regularComplexDimension)
        Z.regularGeometricTrace_degree (Z.regularAmbientCohomologyRestriction (p + p) a)
        (Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) K (2 * Z.regularComplexDimension) b) :=
  Duality.Poincare.CompactTraceEvaluation.complexManifoldOrdinaryCap_openCompactRelativeTrace_evaluation V.complexDimension
    Z.regularAmbientOpen K (p + p) (2 * Z.regularComplexDimension)
    Z.regularGeometricTrace_degree ⟨p, rfl⟩ a b

/-- The actual cap of the geometric class has, at every compact support,
exactly the proper relative trace of the regular locus's fundamental class.
This is equality in relative homology, proved using the full field UCT. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleFundamentalClass_compactTrace (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (K : Compacts Z.regularAmbientSpace) :
    Z.regularAmbientHomologyTrace K (2 * Z.regularComplexDimension)
        Z.geometricCycleFundamentalClass =
      AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
        Z.isProperMap_regularComplementTopCatMap (K : Set Z.regularAmbientSpace)
        K.isCompact (2 * Z.regularComplexDimension)
        Z.regularRationalLocallyFiniteFundamentalClass := by
  apply (AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeScalarHomology_eq_iff_evaluation ℚ (TopCat.of Z.regularAmbientSpace)
    (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) _ _).mpr
  intro b
  change AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of Z.regularAmbientSpace)
    (K : Set Z.regularAmbientSpace)ᶜ (2 * Z.regularComplexDimension) b
    (Z.regularAmbientHomologyTrace K (2 * Z.regularComplexDimension)
      (Duality.Poincare.CompactMeaning.complexManifoldOrdinaryCap V.complexDimension (M := V.analyticSpace)
        (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
        Z.geometricCycleClass)) = _
  rw [Z.regularAmbientHomologyTrace_cap_evaluation]
  exact Z.geometricCycleClass_compactStage_nativeCompactTrace K b

/-- The same relative homology equality with the original integral
compact fundamental class and its unit rational coefficient shown explicitly. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleFundamentalClass_compactTrace_integralPushforward
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (K : Compacts Z.regularAmbientSpace) :
    Z.regularAmbientHomologyTrace K (2 * Z.regularComplexDimension)
        Z.geometricCycleFundamentalClass =
      HomologicalComplex.homologyMap
        (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ Z.regularComplementTopCatMap
          (A := (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))ᶜ)
          (B := (K : Set Z.regularAmbientSpace)ᶜ) (fun _ hx => hx))
        (2 * Z.regularComplexDimension)
        ((AlgebraicGeometry.CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of Z.regularAnalyticSpace)
          (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))ᶜ
          (2 * Z.regularComplexDimension)).inv
          ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
            (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass Z.regularComplexDimension
              (Z.regularCompactPreimage (K : Set Z.regularAmbientSpace))
              (Z.isCompact_regularCompactPreimage (K : Set Z.regularAmbientSpace)
                K.isCompact)))) := by
  rw [Z.geometricCycleFundamentalClass_compactTrace]
  exact Z.regularNativeFundamentalCompactTrace_eq_compactFundamental
    (K : Set Z.regularAmbientSpace) K.isCompact

/-- The actual ambient cap class is characterized by all these
compact-relative traces. This uses the proved singular-boundary restriction
isomorphism as well as the full compact-support duality. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleClass_unique_of_compactRelativeTraces
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (a : V.rationalCohomology (p + p))
    (ha : ∀ K : Compacts Z.regularAmbientSpace,
      Z.regularAmbientHomologyTrace K (2 * Z.regularComplexDimension)
          (Duality.Poincare.CompactMeaning.complexManifoldOrdinaryCap V.complexDimension (M := V.analyticSpace)
            (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree a) =
        AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
          Z.isProperMap_regularComplementTopCatMap (K : Set Z.regularAmbientSpace)
          K.isCompact (2 * Z.regularComplexDimension)
          Z.regularRationalLocallyFiniteFundamentalClass) :
    a = Z.geometricCycleClass := by
  apply (Z.eq_geometricCycleClass_iff_compactTrace a).mpr
  intro K b
  rw [← Z.regularAmbientHomologyTrace_cap_evaluation K a b, ha K]

/-- Equality to the geometric cycle class is equivalent to the actual
fundamental-cycle compact-relative trace characterization of its cap. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.eq_geometricCycleClass_iff_compactRelativeTraces
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (a : V.rationalCohomology (p + p)) :
    a = Z.geometricCycleClass ↔
      ∀ K : Compacts Z.regularAmbientSpace,
        Z.regularAmbientHomologyTrace K (2 * Z.regularComplexDimension)
            (Duality.Poincare.CompactMeaning.complexManifoldOrdinaryCap V.complexDimension (M := V.analyticSpace)
              (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree a) =
          AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
            Z.isProperMap_regularComplementTopCatMap (K : Set Z.regularAmbientSpace)
            K.isCompact (2 * Z.regularComplexDimension)
            Z.regularRationalLocallyFiniteFundamentalClass := by
  constructor
  · rintro rfl K
    exact Z.geometricCycleFundamentalClass_compactTrace K
  · exact Z.geometricCycleClass_unique_of_compactRelativeTraces a

/-- Among all ambient rational homology classes of the complementary
degree, the actual geometric cap class is uniquely determined by its compact
traces of the regular fundamental cycle. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleFundamentalClass_unique
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V.analyticSpace)).homology
      (2 * Z.regularComplexDimension))
    (hz : ∀ K : Compacts Z.regularAmbientSpace,
      Z.regularAmbientHomologyTrace K (2 * Z.regularComplexDimension) z =
        AlgebraicGeometry.CycleClass.Geometric.RegularFundamentalTrace.Cycles.properLocallyFiniteCompactTrace ℚ Z.regularComplementTopCatMap
          Z.isProperMap_regularComplementTopCatMap (K : Set Z.regularAmbientSpace)
          K.isCompact (2 * Z.regularComplexDimension)
          Z.regularRationalLocallyFiniteFundamentalClass) :
    z = Z.geometricCycleFundamentalClass := by
  let e := Duality.Poincare.Manifold.compactComplexManifoldPoincareDuality V.complexDimension (M := V.analyticSpace)
    (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
  let a : V.rationalCohomology (p + p) := e.inv z
  have ha : Duality.Poincare.CompactMeaning.complexManifoldOrdinaryCap V.complexDimension (M := V.analyticSpace)
      (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree a = z :=
    e.inv_hom_id_apply z
  have ha' : a = Z.geometricCycleClass :=
    Z.geometricCycleClass_unique_of_compactRelativeTraces a (fun K => by rw [ha]; exact hz K)
  rw [← ha, ha']
  rfl

/-- The actual ambient cap class is the unique homology class with all
the regular fundamental cycle's compact-relative traces. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.existsUnique_geometricCycleFundamentalClass (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    ∃! z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of V.analyticSpace)).homology
        (2 * Z.regularComplexDimension),
      Z.HasRegularFundamentalCompactTraces z :=
  ⟨Z.geometricCycleFundamentalClass, Z.geometricCycleFundamentalClass_compactTrace,
    Z.geometricCycleFundamentalClass_unique⟩

/-- Applying the inverse of the actual ambient cap isomorphism to the
characterized homology class gives precisely the geometric cycle class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleFundamentalClass_inversePoincareDuality
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (Duality.Poincare.Manifold.compactComplexManifoldPoincareDuality V.complexDimension (M := V.analyticSpace)
      (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree).inv
        Z.geometricCycleFundamentalClass = Z.geometricCycleClass :=
  (Duality.Poincare.Manifold.compactComplexManifoldPoincareDuality V.complexDimension (M := V.analyticSpace)
    (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree).hom_inv_id_apply
      Z.geometricCycleClass

end DimensionCycleSupport

end

end OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTraceCharacterization
