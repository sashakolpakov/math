import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonPair
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.LocalThom

/-! # Common Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonSupport.BundleCycles

noncomputable section

/-! The two canonical classes on a common divisor chart have the
same literal local support, namely the actual ambient divisor image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
  CycleClass.Thom.Scheme.ProperSupport.Constructions CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.RegularIso
  CycleClass.Thom.Closed.SupportAnalyticImage.Constructions CycleClass.Thom.NormalPair.CommonNeighborhood.Constructions
  CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  [AlgebraicGeometry.IsNoetherian Y.left]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (Z : IrreducibleCloseds X.left)
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (q : ℕ) (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (CycleClass.Thom.Scheme.RegularSupport.Constructions.regularOver X Z))

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [AlgebraicGeometry.IsNoetherian Y.left] in
theorem schemeClosedCycleImage_complement :
    (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) =
      (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z)))ᶜ :=
  congrArg Set.compl (CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.supportImage_range i Z).symm

abbrev schemeCycleCommonImageImmersion := Scheme.ClosedCycleImageImmersion.BundleCycles.schemeLocalClosedCycleImmersion i Z p hp q hq x (CommonPair.BundleCycles.schemeCycleCommonOuterPair i Z p hp q hq x)
  (CommonPair.BundleCycles.schemeCycleCommonOuterPair_spec i Z p hp q hq x).2.1

omit [AlgebraicGeometry.IsNoetherian Y.left] in
theorem schemeCycleCommonImage_range : Set.range (schemeCycleCommonImageImmersion i Z p hp q hq x).regularComplementInclusion =
    Subtype.val ⁻¹' (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ :=
  Scheme.ClosedCycleImageImmersion.BundleCycles.schemeLocalClosedCycleImmersion_range i Z p hp q hq x (CommonPair.BundleCycles.schemeCycleCommonOuterPair i Z p hp q hq x) (CommonPair.BundleCycles.schemeCycleCommonOuterPair_spec i Z p hp q hq x).2.1

omit [AlgebraicGeometry.IsNoetherian Y.left] in
theorem schemeCycleCommonCycle_range : Set.range (schemeCycleCommonImageImmersion i Z p hp q hq x).regularComplementInclusion =
    Subtype.val ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z)) := by
  have hs : (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ = Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z)) := by
    rw [schemeClosedCycleImage_complement i Z, compl_compl]
  exact (schemeCycleCommonImage_range i Z p hp q hq x).trans (congrArg (fun S : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) => Subtype.val ⁻¹' S) hs)

omit [AlgebraicGeometry.IsNoetherian Y.left] in
theorem schemeCycleCommonCycle_mapsTo : Set.MapsTo
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      ((CommonPair.BundleCycles.schemeCycleCommonOuterPair i Z p hp q hq x).openNeighborhood : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
    (Set.range (schemeCycleCommonImageImmersion i Z p hp q hq x).regularComplementInclusion)ᶜ
    (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z)))ᶜ :=
  LocalThom.BundleCycles.schemeCycleLocalMapsTo Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (CommonPair.BundleCycles.schemeCycleCommonOuterPair i Z p hp q hq x).openNeighborhood
    (schemeCycleCommonImageImmersion i Z p hp q hq x) (schemeCycleCommonCycle_range i Z p hp q hq x)

omit [AlgebraicGeometry.IsNoetherian Y.left] in
theorem schemeCycleCommonGysin_mapsTo : Set.MapsTo
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      ((CommonPair.BundleCycles.schemeCycleCommonOuterPair i Z p hp q hq x).openNeighborhood : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
    (Set.range (schemeCycleCommonImageImmersion i Z p hp q hq x).regularComplementInclusion)ᶜ
    (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) := by
  intro y hy
  by_contra hn
  exact hy ((Set.ext_iff.mp (schemeCycleCommonImage_range i Z p hp q hq x) y).mpr hn)

omit [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
omit [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [AlgebraicGeometry.IsNoetherian Y.left] in
theorem schemeClosedImageRegularPoint_surjective : Function.Surjective (CommonPair.BundleCycles.schemeClosedImageRegularPoint i Z) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph (CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.RegularIso.regularSupportImageIso i Z)).surjective

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.CommonSupport.BundleCycles
