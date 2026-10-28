import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.SupportRange
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.GraphProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericClass

/-! # Whole Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.WholeSupport.BundleCycles

noncomputable section

/-! The generic-point support of a smooth integral source is the entire source. Its actual finite support cover is therefore an open subscheme of that source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions

abbrev wholeSchemeSupport (S : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral S.left] : IrreducibleCloseds S.left :=
  irreducibleSetEquivPoints.symm (genericPoint S.left)

variable {S N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
  [IsIntegral N.left] [Smooth N.hom] (k : S ⟶ N) [IsFinite k.left]

instance wholeSupportToAmbient_isIso : IsIso (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient S (wholeSchemeSupport S)).left :=
  LineBundle.GenericClass.Cycles.genericPointSupport_isIso S.left

omit [Smooth S.hom] in
theorem wholeSupport_analytic_range : Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion S (wholeSchemeSupport S)) = Set.univ := by
  rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range]
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying ⁻¹' closure {genericPoint S.left} = Set.univ
  rw [(genericPoint_spec S.left).def]
  exact Set.preimage_univ

instance finiteWholeSourceAmbient_open :
    IsOpenImmersion (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (wholeSchemeSupport S)).left := by
  have he : FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (wholeSchemeSupport S) =
      CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver S (wholeSchemeSupport S)) (FiniteSupport.Cover.BundleCycles.finiteSupportSourceOpen k (wholeSchemeSupport S)) ≫
        CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient S (wholeSchemeSupport S) := FiniteSupport.Cover.BundleCycles.finiteSupportSourceToRegular_ambient k (wholeSchemeSupport S)
  rw [he]
  change IsOpenImmersion ((CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver S (wholeSchemeSupport S))
    (FiniteSupport.Cover.BundleCycles.finiteSupportSourceOpen k (wholeSchemeSupport S))).left ≫ (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient S (wholeSchemeSupport S)).left)
  infer_instance

omit [AlgebraicGeometry.IsIntegral N.left] in
theorem finiteWholeSourceAmbient_covers (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map k y ∈ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k (wholeSchemeSupport S)) :
    y ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportSourceAmbientMap k (wholeSchemeSupport S))) := by
  apply FiniteSupport.SupportRange.BundleCycles.finiteSupportFullSupport_point_mem_cover_range k (wholeSchemeSupport S) y _ hy
  rw [wholeSupport_analytic_range]
  trivial

omit [AlgebraicGeometry.IsIntegral N.left] in
theorem finiteWholeImage_dimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (wholeSchemeSupport S)) N.hom =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom := by
  have hs := FiniteSupport.Cover.BundleCycles.finiteSupportSourceOver_dimension k (wholeSchemeSupport S)
  have ht := FiniteSupport.Cover.BundleCycles.finiteSupportTargetOver_dimension k (wholeSchemeSupport S)
  have hc := FiniteSupport.Cover.BundleCycles.finiteSupportCover_dimensions_eq k (wholeSchemeSupport S)
  have hrs := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq S (wholeSchemeSupport S)
  have hrt := CycleClass.Thom.Scheme.RegularSupport.Constructions.regularDimension_eq N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k (wholeSchemeSupport S))
  have hg := LineBundle.GenericClass.Cycles.genericPointSupport_dimension S.left S.hom
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (wholeSchemeSupport S) S.hom = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension S.hom at hg
  have hn := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension S.hom
  omega

omit [AlgebraicGeometry.IsIntegral S.left] [Smooth S.hom] [AlgebraicGeometry.IsIntegral N.left] in
theorem finiteSupportTargetAmbientMap_mem_retained (Z : IrreducibleCloseds S.left)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (FiniteSupport.Cover.BundleCycles.finiteSupportTargetOver k Z)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k Z) x ∈ FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen k Z := by
  have he : FiniteSupport.Cover.BundleCycles.finiteSupportTargetAmbientMap k Z =
      CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k Z)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k Z) ≫
        CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k Z) := FiniteSupport.Cover.BundleCycles.finiteSupportTargetToRegular_ambient k Z
  have he' := (congrArg (fun m : FiniteSupport.Cover.BundleCycles.finiteSupportTargetOver k Z ⟶ N => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map m x) he).trans
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp
      (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.openSchemeInclusion (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k Z)) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k Z))
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k Z)) x)
  rw [he']
  change ¬ CycleClass.Geometric.GenericPoint.reducedSupportι (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k Z) ((FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k Z).ι (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x)) ∈
    CycleClass.Thom.Scheme.SmoothSupportOpen.Constructions.supportOpenBoundary N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k Z) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k Z)
  intro hx
  have hh := Set.ext_iff.mp (Scheme.SupportDenseOpenImage.BundleCycles.schemeSupportOpenBoundary_preimage N (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport k Z) (FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k Z))
    ((FiniteSupport.Cover.BundleCycles.finiteSupportGoodOpen k Z).ι (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x))
  exact (hh.mp hx) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x).property

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.WholeSupport.BundleCycles
