import OAI.AlgebraicTopology.DeRham.Comparison.CycleIsomorphismDiffeomorph
import OAI.AlgebraicTopology.DeRham.Comparison.RegularAmbientCohomology

/-! # Regular Ambient Naturality -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RegularAmbientNaturality.DimensionCycleSupport

noncomputable section

/-!
# Ordinary cohomology naturality of the actual regular ambient open set

These maps restrict an algebraic isomorphism to the complements of the
corresponding singular boundaries. The ordinary restriction square is the
actual commutative square of continuous point maps.
-/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- Ordinary cohomology pullback of the genuine regular ambient diffeomorphism. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyPullbackOfIso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace) n ⟶
      Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) n :=
  Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
    (TopCat.isoOfHomeo
      (X := TopCat.of Z.regularAmbientSpace)
      (Y := TopCat.of (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace)
      (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z 1).toHomeomorph).hom n

/-- This is the same ordinary pullback as that of the literal continuous subspace map. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyPullbackOfIso_eq_subspace (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyPullbackOfIso e Z n =
      Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom)
          (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_boundaryComplement e Z)) n := rfl

/-- Ordinary ambient pullback commutes with restriction off the actual singular boundary. -/
@[reassoc]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyRestriction_iso_naturality
    (e : V.toOver ≅ W.toOver) (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (n : ℕ) :
    AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom n ≫
        Z.regularAmbientCohomologyRestriction n =
      (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientCohomologyRestriction n ≫
        AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyPullbackOfIso e Z n := by
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyPullbackOfIso_eq_subspace]
  change Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom) n ≫
      Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) Z.analyticSingularBoundaryᶜ) n =
    Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of W.analyticSpace)
          (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).analyticSingularBoundaryᶜ) n ≫
      Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom)
          (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_boundaryComplement e Z)) n
  rw [← Cohomology.Singular.Functor.singularCohomologyPullback_comp, ← Cohomology.Singular.Functor.singularCohomologyPullback_comp,
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap_inclusion]
  rfl

/-- The actual restriction square evaluated on an ordinary rational cohomology class. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyRestriction_iso_naturality_apply
    (e : V.toOver ≅ W.toOver) (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (n : ℕ)
    (a : W.rationalCohomology n) :
    Z.regularAmbientCohomologyRestriction n
        (AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback e.hom n a) =
      AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyPullbackOfIso e Z n
        ((AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientCohomologyRestriction n a) :=
  ConcreteCategory.congr_hom (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientCohomologyRestriction_iso_naturality e Z n) a

end

end OAI.AlgebraicTopology.DeRham.Comparison.RegularAmbientNaturality.DimensionCycleSupport
