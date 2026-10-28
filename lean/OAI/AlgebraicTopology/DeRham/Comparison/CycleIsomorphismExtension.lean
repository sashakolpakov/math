import OAI.AlgebraicTopology.DeRham.Comparison.CycleExtensionNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism
import OAI.AlgebraicGeometry.CycleClass.Geometric.RegularSupportIsomorphism
import OAI.AlgebraicGeometry.CycleClass.Geometric.SingularBoundaryPurity
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveMaps

/-! # Cycle Isomorphism Extension -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CycleIsomorphismExtension.DimensionCycleSupport

noncomputable section

/-!
The actual cycle-extension square under an isomorphism of complex varieties.

Every map of pairs is obtained from the genuine map on complex points.
The support and singular-boundary conditions follow from exact preimage
identities of the corresponding algebraic loci. The rational extension
theorems use the proved singular-boundary vanishings, with no purity or
class hypothesis remaining.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
variable {R : Type} [Ring R]

/-- On the genuine analytic spaces, the transported support has precisely
the original support as its inverse image. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSupport_preimage_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom ⁻¹'
        Set.range (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).analyticInclusion =
      Set.range Z.analyticInclusion := by
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.range_analyticInclusion, AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.range_analyticInclusion]
  exact AlgebraicGeometry.CycleClass.Geometric.RegularSupportIsomorphism.complexPoints_preimage_supportIso e Z.val

/-- The analogous exact inverse-image identity holds for the actual
singular boundaries. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSingularBoundary_preimage_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom ⁻¹'
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).analyticSingularBoundary =
      Z.analyticSingularBoundary := by
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : Smooth W.toOver.hom := W.presentation.smooth
  exact AlgebraicGeometry.CycleClass.Geometric.RegularSupportIsomorphism.complexPoints_preimage_singularBoundaryIso e Z.val

/-- The actual analytic isomorphism maps the original support complement
into the complement of its transported support. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_supportComplement (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Set.MapsTo (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom)
      (Set.range Z.analyticInclusion)ᶜ
      (Set.range (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).analyticInclusion)ᶜ := by
  intro x hx
  change x ∉ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom ⁻¹'
    Set.range (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).analyticInclusion
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSupport_preimage_iso]
  exact hx

/-- It also maps the actual singular-boundary complement into the
transported singular-boundary complement. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_boundaryComplement (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Set.MapsTo (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom)
      Z.analyticSingularBoundaryᶜ
      (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).analyticSingularBoundaryᶜ := by
  intro x hx
  change x ∉ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom ⁻¹'
    (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).analyticSingularBoundary
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSingularBoundary_preimage_iso]
  exact hx

/-- Pullback on actual cohomology supported on corresponding algebraic loci. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.supportCohomologyPullbackOfIso (M : ModuleCat.{0} R) (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of W.analyticSpace)
        (Set.range (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).analyticInclusion)ᶜ n ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of V.analyticSpace)
        (Set.range Z.analyticInclusion)ᶜ n :=
  Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap M (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom)
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_supportComplement e Z) n

/-- Pullback of the actual regular-locus Thom pairs, induced by the
restriction of the analytic isomorphism to the boundary complements. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularCohomologyPullbackOfIso (M : ModuleCat.{0} R) (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    Cohomology.Singular.RelativeSequence.relativeSingularCohomology M
        (TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace)
        (Set.range (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplementInclusion)ᶜ n ⟶
      Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of Z.regularAmbientSpace)
        (Set.range Z.regularComplementInclusion)ᶜ n :=
  AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularPairCohomologyPullback M Z (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z)
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom)
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_boundaryComplement e Z) (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_supportComplement e Z) n

/-- The degree-`2p` extension is natural under actual isomorphisms. All
four singular-boundary obstruction groups vanish by the proved purity theorem. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalRegularToSupport_of_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    ((AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularToSupportCohomologyIso
        (ModuleCat.of ℚ ℚ) (2 * p)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_isZero
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_add_one_isZero).hom ≫
      AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.supportCohomologyPullbackOfIso (ModuleCat.of ℚ ℚ) e Z (2 * p) =
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularCohomologyPullbackOfIso (ModuleCat.of ℚ ℚ) e Z (2 * p) ≫
      (Z.regularToSupportCohomologyIso (ModuleCat.of ℚ ℚ) (2 * p)
        Z.singularBoundaryRationalCohomology_two_mul_isZero
        Z.singularBoundaryRationalCohomology_two_mul_add_one_isZero).hom :=
  AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToSupportCohomologyIso_naturality (ModuleCat.of ℚ ℚ)
    Z (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom)
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_boundaryComplement e Z) (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_supportComplement e Z) (2 * p)
    Z.singularBoundaryRationalCohomology_two_mul_isZero
    Z.singularBoundaryRationalCohomology_two_mul_add_one_isZero
    (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_isZero
    (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_add_one_isZero

/-- Extending and forgetting support commutes with the actual rational
Betti pullback induced by the variety isomorphism. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalRegularToAbsolute_of_iso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularToAbsoluteCohomology
        (ModuleCat.of ℚ ℚ) (2 * p)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_isZero
        (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_add_one_isZero ≫
      AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (2 * p) =
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularCohomologyPullbackOfIso (ModuleCat.of ℚ ℚ) e Z (2 * p) ≫
      Z.regularToAbsoluteCohomology (ModuleCat.of ℚ ℚ) (2 * p)
        Z.singularBoundaryRationalCohomology_two_mul_isZero
        Z.singularBoundaryRationalCohomology_two_mul_add_one_isZero :=
  AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularToAbsoluteCohomology_naturality (ModuleCat.of ℚ ℚ)
    Z (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom)
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_boundaryComplement e Z) (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_supportComplement e Z) (2 * p)
    Z.singularBoundaryRationalCohomology_two_mul_isZero
    Z.singularBoundaryRationalCohomology_two_mul_add_one_isZero
    (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_isZero
    (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_add_one_isZero

/-- The support extension square evaluated on an arbitrary genuine
regular-locus relative cohomology class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalRegularToSupport_of_iso_apply (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace)
      (Set.range (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplementInclusion)ᶜ (2 * p)) :
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.supportCohomologyPullbackOfIso (ModuleCat.of ℚ ℚ) e Z (2 * p)
        (((AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularToSupportCohomologyIso
          (ModuleCat.of ℚ ℚ) (2 * p)
          (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_isZero
          (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_add_one_isZero).hom c) =
      (Z.regularToSupportCohomologyIso (ModuleCat.of ℚ ℚ) (2 * p)
        Z.singularBoundaryRationalCohomology_two_mul_isZero
        Z.singularBoundaryRationalCohomology_two_mul_add_one_isZero).hom
          (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularCohomologyPullbackOfIso (ModuleCat.of ℚ ℚ) e Z (2 * p) c) :=
  ConcreteCategory.congr_hom (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalRegularToSupport_of_iso e Z) c

/-- The absolute extension square evaluated on a genuine regular-locus class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalRegularToAbsolute_of_iso_apply (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace)
      (Set.range (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplementInclusion)ᶜ (2 * p)) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom (2 * p)
        ((AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularToAbsoluteCohomology
          (ModuleCat.of ℚ ℚ) (2 * p)
          (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_isZero
          (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).singularBoundaryRationalCohomology_two_mul_add_one_isZero c) =
      Z.regularToAbsoluteCohomology (ModuleCat.of ℚ ℚ) (2 * p)
        Z.singularBoundaryRationalCohomology_two_mul_isZero
        Z.singularBoundaryRationalCohomology_two_mul_add_one_isZero
          (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularCohomologyPullbackOfIso (ModuleCat.of ℚ ℚ) e Z (2 * p) c) :=
  ConcreteCategory.congr_hom (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.rationalRegularToAbsolute_of_iso e Z) c

end

end OAI.AlgebraicTopology.DeRham.Comparison.CycleIsomorphismExtension.DimensionCycleSupport
