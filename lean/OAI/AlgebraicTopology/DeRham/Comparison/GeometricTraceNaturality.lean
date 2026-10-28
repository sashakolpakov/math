import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTrace
import OAI.AlgebraicTopology.DeRham.Comparison.CycleIsomorphismDiffeomorph
import OAI.AlgebraicTopology.DeRham.Comparison.CycleIsomorphismDimensions
import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTraceDimension

/-! # Geometric Trace Naturality -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.GeometricTraceNaturality

noncomputable section

/-!
# Geometric regular-cycle trace under algebraic isomorphisms

The actual isomorphism of reduced regular loci commutes with their proper
inclusions in the ambient singular-boundary complements. Proper pullback
therefore intertwines restriction to the regular loci. The canonical complex
top trace then identifies the two geometric functionals, with only the
explicit transport along the proved equality of their dimensions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTraceDimension
open scoped ContDiff _root_.Manifold

set_option backward.isDefEq.respectTransparency false

private theorem properPullback_degree_transport {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) {i j : ℕ} (h : i = j)
    (a : Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) Y i) :
    Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) f hf j
        (eqToHom (congrArg
          (fun n => Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) Y n) h) a) =
      eqToHom (congrArg
        (fun n => Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) X n) h)
        (Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ) f hf i a) := by
  subst j
  rfl

namespace DimensionCycleSupport

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The actual algebraic isomorphism between the regular loci of corresponding
reduced supports, retaining both structure maps over the complex base. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularOverIsoOfIso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularOver ≅ (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularOver := by
  let : Smooth V.structureMap := V.presentation.smooth
  let : Smooth W.structureMap := W.presentation.smooth
  exact AlgebraicGeometry.CycleClass.Geometric.RegularSupportIsomorphism.regularSupportOverIso ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) Z.val
    V.structureMap W.structureMap e.hom.w

/-- The regular-locus isomorphism commutes with its genuine algebraic
inclusions into the two ambient varieties. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularOverIsoOfIso_hom_toAmbient (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularOverIsoOfIso e Z).hom ≫
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularToAmbient =
      Z.regularToAmbient ≫ e.hom := by
  let : Smooth V.structureMap := V.presentation.smooth
  let : Smooth W.structureMap := W.presentation.smooth
  apply Over.OverMorphism.ext
  exact AlgebraicGeometry.CycleClass.Geometric.RegularSupportIsomorphism.regularSupportSchemeIso_hom_inclusion
    ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e) Z.val V.structureMap W.structureMap e.hom.w

/-- Native analytic realization of the genuine regular-locus isomorphism. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusDiffeomorphOfIso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) :
    Diffeomorph (𝓘(ℂ, Z.regularAnalyticModel))
      (𝓘(ℂ, (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAnalyticModel))
      Z.regularAnalyticSpace (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAnalyticSpace r := by
  let : IsIntegral Z.regularOver.left := inferInstanceAs (IsIntegral Z.regularScheme)
  let : Smooth Z.regularOver.hom := inferInstanceAs (Smooth Z.regularToBase)
  let : IsIntegral (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularOver.left :=
    inferInstanceAs (IsIntegral (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularScheme)
  let : Smooth (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularOver.hom :=
    inferInstanceAs (Smooth (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularToBase)
  exact AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSchemeDiffeomorph.nativeSchemeDiffeomorph (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularOverIsoOfIso e Z) r

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusDiffeomorphOfIso_apply (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) (x : Z.regularAnalyticSpace) :
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusDiffeomorphOfIso e Z r x =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularOverIsoOfIso e Z).hom x := rfl

/-- The actual continuous regular-locus isomorphism, used by proper
compact-support pullback. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusTopCatIsoOfIso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    TopCat.of Z.regularAnalyticSpace ≅
      TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAnalyticSpace :=
  TopCat.isoOfHomeo (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusDiffeomorphOfIso e Z 1).toHomeomorph

/-- The actual continuous isomorphism of the ambient boundary complements. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientTopCatIsoOfIso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    TopCat.of Z.regularAmbientSpace ≅
      TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace :=
  TopCat.isoOfHomeo (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z 1).toHomeomorph

/-- The analytic square uses the genuine proper regular inclusions. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementTopCatMap_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularComplementTopCatMap ≫ (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientTopCatIsoOfIso e Z).hom =
      (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusTopCatIsoOfIso e Z).hom ≫
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplementTopCatMap := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map Z.regularToAmbient x) =
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularToAmbient
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularOverIsoOfIso e Z).hom x)
  rw [← AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, ← AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp,
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularOverIsoOfIso_hom_toAmbient]

/-- Proper pullback on compact-support cohomology commutes with the actual
regular-locus square, in every degree. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementProperPullback_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientTopCatIsoOfIso e Z).hom
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z 1).toHomeomorph.isProperMap n ≫
      Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap n =
    Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplementTopCatMap
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).isProperMap_regularComplementTopCatMap n ≫
      Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusTopCatIsoOfIso e Z).hom
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusDiffeomorphOfIso e Z 1).toHomeomorph.isProperMap n := by
  rw [← Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback_comp,
    ← Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback_comp]
  congr 1
  exact AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementTopCatMap_iso e Z

/-- The test-class pullback is an actual isomorphism. Its degree transport
is exactly the proved equality of the two regular-locus dimensions. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace)
        (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension) ≅
      Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension) :=
  Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z 1).toHomeomorph
      (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension) ≪≫
    eqToIso (congrArg
      (fun n => Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of Z.regularAmbientSpace) n)
      (congrArg (fun n => 2 * n) (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_iso e Z)))

/-- Explicit formula for the test-class isomorphism: genuine proper
pullback followed by the degree equality, and no chosen linear equivalence. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso_hom (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso e Z).hom =
      Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientTopCatIsoOfIso e Z).hom
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z 1).toHomeomorph.isProperMap
        (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension) ≫
      eqToHom (congrArg
        (fun n => Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) n)
        (congrArg (fun n => 2 * n) (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_iso e Z))) := by
  unfold AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientTopCatIsoOfIso
  rw [Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback_homeomorph]
  rfl

/-- Elementwise formula in terms of the literal ambient diffeomorphism,
for use with ordinary/compact-support pairing naturality. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso_hom_apply (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (b : Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace)
      (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension)) :
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso e Z).hom b =
      eqToHom (congrArg
        (fun n => Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAmbientSpace) n)
        (congrArg (fun n => 2 * n) (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_iso e Z)))
        (Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
          (TopCat.isoOfHomeo (X := TopCat.of Z.regularAmbientSpace)
            (Y := TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace)
            (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z 1).toHomeomorph).hom
          (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z 1).toHomeomorph.isProperMap
          (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension) b) :=
  ConcreteCategory.congr_hom (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso_hom e Z) b

/-- The actual geometric regular-cycle trace is invariant under algebraic
isomorphism. Every test class is transported by the genuine ambient
diffeomorphism and the proved numerical dimension equality. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (b : Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace)
      (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension)) :
    Z.regularGeometricTrace ((AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso e Z).hom b) =
      (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularGeometricTrace b := by
  simp only [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_apply]
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso_hom_apply,
    properPullback_degree_transport Z.regularComplementTopCatMap
      Z.isProperMap_regularComplementTopCatMap
      (congrArg (fun n => 2 * n) (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_iso e Z))]
  have hs := ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplementProperPullback_iso e Z
      (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension)) b
  change Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
      Z.regularComplementTopCatMap Z.isProperMap_regularComplementTopCatMap
      (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension)
      (Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientTopCatIsoOfIso e Z).hom
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z 1).toHomeomorph.isProperMap
        (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension) b) =
    Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
      (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusTopCatIsoOfIso e Z).hom
      (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusDiffeomorphOfIso e Z 1).toHomeomorph.isProperMap
      (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension)
      (Duality.Poincare.ProperCompactSupportPullback.compactSupportedCohomologyProperPullback (ModuleCat.of ℚ ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplementTopCatMap
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).isProperMap_regularComplementTopCatMap
        (2 * (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplexDimension) b) at hs
  have hc := congrArg
    (fun a => Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace Z.regularComplexDimension (M := Z.regularAnalyticSpace)
      (eqToHom (congrArg
        (fun n => Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
          (TopCat.of Z.regularAnalyticSpace) n)
        (congrArg (fun n => 2 * n) (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_iso e Z))) a)) hs
  exact hc.trans (Duality.Poincare.ComplexManifoldTraceDimension.complexManifoldTrace_diffeomorph_of_dimension_eq_apply
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_iso e Z) (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularLocusDiffeomorphOfIso e Z 1) _)

/-- The same invariance as an equality of actual module morphisms. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_naturality (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTracePullbackIsoOfIso e Z).hom ≫
        ModuleCat.ofHom Z.regularGeometricTrace =
      ModuleCat.ofHom (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularGeometricTrace := by
  apply ConcreteCategory.hom_ext
  exact AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricTrace_iso e Z

end DimensionCycleSupport

end

end OAI.AlgebraicTopology.DeRham.Comparison.GeometricTraceNaturality
