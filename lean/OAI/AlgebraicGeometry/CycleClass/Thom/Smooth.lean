import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.OpenNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.GeometricTrace
import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Degree

/-! # Smooth -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Smooth.Constructions

noncomputable section

/-! The actual whole-ambient Thom class of a smooth support agrees with
its supported algebraic cycle class and its independently defined
geometric Betti class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.SmoothImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.OpenNaturality.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Degree.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.GeometricTrace.Constructions.HigherThom
  Normal.Product.Constructions.Class ExteriorCupForget.Constructions Cycle.Degree.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
  [Smooth Z.structureMap]

theorem smoothThom_supportedClass :
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of V.analyticSpace) A (2 * p)) (congrArg Set.compl (SmoothImmersion.Constructions.regular_range_eq_support Z)))
      (SmoothImmersion.Constructions.smoothCycleImmersion Z).regularThomClass = Z.rationalSupportedCycleClass := by
  apply Z.rationalSupportedCycleClass_unique
  change (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
    Z.analyticSingularBoundaryᶜ (Set.range Z.analyticInclusion)ᶜ (2 * p) ≫
      (Z.regularThomCohomologyIso (ModuleCat.of ℚ ℚ) (2 * p)).inv) _ = _
  rw [Geometric.DimensionCycles.DimensionCycleSupport.relativeCohomologyTripleRestriction_regularThom]
  have hc := Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) Z.analyticSingularBoundaryᶜ)
    (congrArg Set.compl (SmoothImmersion.Constructions.regular_range_eq_support Z))
    (Open.NormalPairRestriction.Constructions.openAmbientTransportMapsTo Z.regularComplementInclusion
      Subtype.val Z.regularAmbientOpen.isOpenEmbedding')
    (fun x hx => (Z.mem_regularThomComplement_iff x).mp hx) (2 * p)
    (SmoothImmersion.Constructions.smoothCycleImmersion Z).regularThomClass
  apply hc.trans
  exact OpenNaturality.Constructions.complexThomClassInDegree_openAmbient Z.regularAmbientOpen Z.regularComplementInclusion
    (Z.contMDiff_regularComplementInclusion ω) Z.mfderiv_regularComplementInclusion_injective
    Z.isClosedEmbedding_regularComplementInclusion
    (SmoothImmersion.Constructions.smoothCycleImmersion Z).holomorphic (SmoothImmersion.Constructions.smoothCycleImmersion Z).differential_injective
    (SmoothImmersion.Constructions.regular_closed Z) p Z.regularComplement_complexImmersionCodimension

theorem smoothThom_absoluteClass :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range Z.regularAnalyticToAmbient)ᶜ (2 * p) (SmoothImmersion.Constructions.smoothCycleImmersion Z).regularThomClass =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range Z.analyticInclusion)ᶜ (2 * p) Z.rationalSupportedCycleClass := by
  rw [← smoothThom_supportedClass Z]
  exact (ExteriorCupForget.Constructions.relativeInclusion_supportCast (TopCat.of V.analyticSpace)
    (congrArg Set.compl (SmoothImmersion.Constructions.regular_range_eq_support Z)) (2 * p) _).symm

theorem smoothThom_geometricClass :
    cast (congrArg (fun n => (V.rationalCohomology n : Type)) (two_mul p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (Set.range Z.regularAnalyticToAmbient)ᶜ (2 * p) (SmoothImmersion.Constructions.smoothCycleImmersion Z).regularThomClass) =
    Z.geometricCycleClass := by
  rw [smoothThom_absoluteClass, ← Cycle.Degree.Constructions.Class.rationalCycleClass_as_cast, GeometricTrace.Constructions.HigherThom.rationalCycleClass_eq_geometric]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Smooth.Constructions
