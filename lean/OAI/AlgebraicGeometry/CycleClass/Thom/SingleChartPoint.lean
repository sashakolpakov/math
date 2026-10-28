import OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartComplexManifold
import OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport

/-! # Single Chart Point -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartPoint.Constructions.Class

noncomputable section

/-! The canonical point class in a specified global chart is its centered normal-coordinate pullback. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartComplexManifold.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse.Constructions.CanonicalNaturality
open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDualCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] (e : M ≃ₜ (Fin d → ℂ))

def centeredChartMap (x : M) : TopCat.of M ⟶ TopCat.of (Fin d → ℂ) :=
  (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of (Fin d → ℂ)) e).hom ≫
    (TopCat.isoOfHomeo (X := TopCat.of (Fin d → ℂ)) (Y := TopCat.of (Fin d → ℂ))
      (Homeomorph.subRight (e x))).hom

theorem centeredChartMapsTo (x : M) : Set.MapsTo (centeredChartMap d e x) ({x}ᶜ) ({0}ᶜ) :=
  (CanonicalLocalDualCoordinates.Constructions.translationMapsTo d (e x)).comp
    (LocalDualLocalInverse.Constructions.CanonicalNaturality.injectivePunctureMapsTo
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of (Fin d → ℂ)) e).hom e.injective x)

variable [Nonempty M] [T2Space M]

theorem canonicalLocalDual_centeredChart (x : M) :
    letI := SingleChartComplexManifold.Constructions.coordinateChartedSpace d e
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (centeredChartMap d e x)
      (centeredChartMapsTo d e x) (2 * d) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d) =
        CanonicalLocalDual.Constructions.canonicalLocalDual d x := by
  let := SingleChartComplexManifold.Constructions.coordinateChartedSpace d e
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of (Fin d → ℂ)) e).hom
      (TopCat.isoOfHomeo (X := TopCat.of (Fin d → ℂ)) (Y := TopCat.of (Fin d → ℂ))
        (Homeomorph.subRight (e x))).hom
      (LocalDualLocalInverse.Constructions.CanonicalNaturality.injectivePunctureMapsTo _ e.injective x) (CanonicalLocalDualCoordinates.Constructions.translationMapsTo d (e x)) (2 * d))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass d)
  refine hc.symm.trans ?_
  refine (congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of (Fin d → ℂ)) e).hom
    (LocalDualLocalInverse.Constructions.CanonicalNaturality.injectivePunctureMapsTo _ e.injective x) (2 * d))
    (CanonicalLocalDualCoordinates.Constructions.canonicalLocalDual_translation d (e x))).trans ?_
  exact SingleChartComplexManifold.Constructions.pointClass_chart d e x

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartPoint.Constructions.Class
