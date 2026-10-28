import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportNeighborhoodDetection

/-! # Closed Cycle Gysin Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleGysinClass.BundleCycles

noncomputable section

/-! The genuine supported Gysin map of a smooth closed algebraic
immersion takes the canonical class of every source cycle, including singular cycles in arbitrary codimension, to the canonical supported class of its actual ambient image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
  CycleClass.Thom.Scheme.ProperSupport.Constructions CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.RegularIso
  CycleClass.Thom.Closed.SupportAnalyticImage.Constructions CycleClass.Thom.NormalPair.CommonNeighborhood.Constructions
  CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  [AlgebraicGeometry.IsNoetherian Y.left]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (Z : IrreducibleCloseds X.left)
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (q : ℕ) (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.GysinRestriction.Constructions.ThomClass OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction
  CycleClass.Thom.Normal.Product.Constructions.Class

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)

theorem schemeClosedCycleGysinClass_eq_imageClass :
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) A (2 * (p + q))) (SchemeCycle.CommonSupport.BundleCycles.schemeClosedCycleImage_complement i Z))
      (ClosedCycleGysin.BundleCycles.schemeClosedCycleGysinClass i Z p hp q hq a ha) = (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq)) := by
  classical
  let D := CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z
  let s : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y D) → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z) :=
    fun y => Classical.choose (SchemeCycle.CommonSupport.BundleCycles.schemeClosedImageRegularPoint_surjective i Z y)
  have hs (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y D)) : SchemeCycle.CommonPair.BundleCycles.schemeClosedImageRegularPoint i Z (s y) = y :=
    Classical.choose_spec (SchemeCycle.CommonSupport.BundleCycles.schemeClosedImageRegularPoint_surjective i Z y)
  let U : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y D) → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :=
    fun y => (SchemeCycle.CommonPair.BundleCycles.schemeCycleCommonOuterPair i Z p hp q hq (s y)).openNeighborhood
  have hU (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver Y D)) : CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Y D y ∈ U y := by
    have he : CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Y D y = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion X Z (s y)) :=
      (congrArg (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularInclusion Y D) (hs y).symm).trans (SchemeCycle.CommonPair.BundleCycles.schemeClosedImageRegularPoint_ambient i Z (s y))
    exact (congrArg (fun t => t ∈ U y) he).mpr (SchemeCycle.CommonPair.BundleCycles.schemeCycleCommonOuterPair i Z p hp q hq (s y)).point_mem_neighborhood
  apply SupportNeighborhoodDetection.BundleCycles.schemeSupportedClass_eq_of_regular_neighborhoods Y D (p + q) (ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq) U hU
  intro y
  let C := SchemeCycle.CommonSupport.BundleCycles.schemeCycleCommonImageImmersion i Z p hp q hq (s y)
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (U y : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
  have he : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y D))ᶜ (U y) =
      (Set.range C.regularComplementInclusion)ᶜ :=
    (congrArg Set.compl (SchemeCycle.CommonSupport.BundleCycles.schemeCycleCommonCycle_range i Z p hp q hq (s y))).symm
  let e := AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (U y)) he (2 * (p + q))
  apply e.toLinearEquiv.injective
  have hc (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y D))ᶜ (2 * (p + q))) :=
    CycleClass.Thom.ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast j he
      (show Set.MapsTo j (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y D))ᶜ (U y))
        (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y D))ᶜ from fun _ hy => hy)
      (SchemeCycle.CommonSupport.BundleCycles.schemeCycleCommonCycle_mapsTo i Z p hp q hq (s y)) (2 * (p + q)) b
  have ht := CycleClass.Thom.Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast j (SchemeCycle.CommonSupport.BundleCycles.schemeClosedCycleImage_complement i Z)
    (SchemeCycle.CommonSupport.BundleCycles.schemeCycleCommonGysin_mapsTo i Z p hp q hq (s y)) (SchemeCycle.CommonSupport.BundleCycles.schemeCycleCommonCycle_mapsTo i Z p hp q hq (s y))
    (2 * (p + q)) (ClosedCycleGysin.BundleCycles.schemeClosedCycleGysinClass i Z p hp q hq a ha)
  have hm := SchemeCycle.CommonClass.BundleCycles.schemeCycleGysinClass_eq_imageClass_on_commonChart i Z p hp q hq (s y) a ha
  have hback := hc (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y D (p + q) (ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq))
  exact (hc _).trans (ht.trans (hm.trans hback.symm))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleGysinClass.BundleCycles
