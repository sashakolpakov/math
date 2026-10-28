import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedCycleGysinClass
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.GysinEnlargement

/-! # Intersection Gysin -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.IntersectionGysin.BundleCycles

noncomputable section

/-! The supported Gysin isomorphism carries every canonical source cycle to its actual image class after enlarging both supports to the same intersection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportAnalyticImage.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product.Constructions.Class
open OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (Z : IrreducibleCloseds X.left)
  {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
  (hZ : Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z)) ⊆ Set.range v)

include hZ in
omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeCycleIntersection_source_mapsTo : Set.MapsTo (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ) (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z))ᶜ := by
  intro x hx hz
  obtain ⟨z, hz⟩ := hz
  apply hx
  apply hZ
  rw [CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.supportImage_range]
  exact ⟨z, congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) hz⟩

include hZ in
omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeCycleIntersection_target_mapsTo : Set.MapsTo (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
    (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v)ᶜ
    (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z)))ᶜ := by
  intro y hy hz
  have hr := hz
  rw [CycleClass.Thom.Closed.SupportAnalyticImage.Constructions.supportImage_range] at hr
  obtain ⟨z, hz'⟩ := hr
  exact hy ⟨⟨CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion X Z z, hz'⟩, hZ hz⟩

include hZ in
omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem schemeCycleIntersection_complement_le : (Set.range v)ᶜ ⊆
    (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) := by
  rw [CommonSupport.BundleCycles.schemeClosedCycleImage_complement]
  exact Set.compl_subset_compl.mpr hZ

variable (hv : IsOpen (Set.range v)ᶜ)
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (q : ℕ) (hq : Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)

theorem schemeCycleIntersectionGysin_imageClass :
    (CycleClass.Thom.Intersection.Gysin.Constructions.intersectionGysinIso (q := q) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) a ha v hv).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
        (schemeCycleIntersection_source_mapsTo i Z v hZ) (2 * q) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z q hq)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (schemeCycleIntersection_target_mapsTo i Z v hZ) (2 * (p + q))
      (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport i Z) (p + q) (Scheme.ClosedImageCodimension.BundleCycles.schemeClosedImage_codimension i Z p hp q hq)) := by
  let hOW := schemeCycleIntersection_complement_le i Z v hZ
  let hW := Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImage_supported i Z p hp
  let hs := CycleClass.Thom.Supported.GysinEnlargement.Constructions.source_mapsTo
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z) v hOW
  let ht := CycleClass.Thom.Supported.GysinEnlargement.Constructions.target_mapsTo
    (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z) hW v hOW
  let b := Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass X Z q hq
  let b' := (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleSourceComplement i Z) (2 * q)).inv b
  have h := ConcreteCategory.congr_hom
    (CycleClass.Thom.Supported.GysinEnlargement.Constructions.globalGysinIso_enlargement (q := q)
      (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleImageOpen i Z) hW v hv hOW a ha) b'
  have hsrc := CycleClass.Thom.Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleSourceComplement i Z).symm
    (schemeCycleIntersection_source_mapsTo i Z v hZ) hs (2 * q) b
  have htgt := CycleClass.Thom.Normal.Product.Constructions.Class.relativeCohomologyMap_targetCast (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
    (CommonSupport.BundleCycles.schemeClosedCycleImage_complement i Z) ht (schemeCycleIntersection_target_mapsTo i Z v hZ)
    (2 * (p + q)) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleGysinClass i Z p hp q hq a ha)
  rw [Scheme.ClosedCycleGysinClass.BundleCycles.schemeClosedCycleGysinClass_eq_imageClass] at htgt
  change (CycleClass.Thom.Intersection.Gysin.Constructions.intersectionGysinIso (q := q) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) a ha v hv).hom
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hs (2 * q) b') =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))) ht
      (2 * (p + q)) (Scheme.ClosedCycleGysin.BundleCycles.schemeClosedCycleGysinClass i Z p hp q hq a ha) at h
  exact (congrArg (CycleClass.Thom.Intersection.Gysin.Constructions.intersectionGysinIso (q := q) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) a ha v hv).hom hsrc.symm).trans
    (h.trans htgt.symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.IntersectionGysin.BundleCycles
