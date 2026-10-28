import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedOpenClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.PreimageSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction

/-! # Closed Class Pullback Generator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedClassPullbackGenerator.BundleCycles

noncomputable section

/-! Actual open pullback of a supported generator, including the empty inverse-image case. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsOpenImmersion i.left] (F : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] [IsOpenImmersion (Over.Hom.left i)] in
theorem schemeClosedPullback_mapsTo : Set.MapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F)ᶜ Fᶜ := fun _ hx => hx

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [IsOpenImmersion (Over.Hom.left i)] in
theorem schemeClosedRelativeGenerator_pullback_expansion (x : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint Y F d) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (schemeClosedPullback_mapsTo i F) (2 * p) (OpenSupportedCycle.BundleCycles.schemeClosedRelativeGenerator Y F d p hd x) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      ((OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_mapsTo Y F d x).comp (schemeClosedPullback_mapsTo i F)) (2 * p)
      (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y (irreducibleSetEquivPoints.symm x.val.val) p
        ((congrArg (fun n => n + p) x.val.property).trans hd)) := by
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
    (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))) (schemeClosedPullback_mapsTo i F)
    (OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_mapsTo Y F d x) (2 * p)
  have he := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr
    (Category.comp_id (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i))
    ((OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_mapsTo Y F d x).comp (schemeClosedPullback_mapsTo i F))
    ((OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_mapsTo Y F d x).comp (schemeClosedPullback_mapsTo i F)) (2 * p)
  exact ConcreteCategory.congr_hom (h.trans he) _

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem schemeClosedRelativeGenerator_pullback_empty (x : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint Y F d)
    (hx : x.val.val ∉ Set.range i.left) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (schemeClosedPullback_mapsTo i F) (2 * p) (OpenSupportedCycle.BundleCycles.schemeClosedRelativeGenerator Y F d p hd x) = 0 := by
  rw [schemeClosedRelativeGenerator_pullback_expansion]
  have he := SchemeCycle.EmptyPullback.BundleCycles.openSupport_preimage_empty_of_generic_not_mem i (irreducibleSetEquivPoints.symm x.val.val)
    (by simpa only [OrderIso.apply_symm_apply] using hx)
  have hm : ∀ z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i z ∈ (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val.val)))ᶜ := by
    intro z hz
    rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range] at hz
    have h : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z ∈ i.left ⁻¹' (irreducibleSetEquivPoints.symm x.val.val : Set Y.left) := hz
    rw [he] at h
    exact h
  have h := DivisorClass.Chern.SupportedDivisorSum.relativeCohomologyMap_zero_of_range_subset (ModuleCat.of ℚ ℚ)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F)ᶜ
    (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val.val)))ᶜ
    ((OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_mapsTo Y F d x).comp (schemeClosedPullback_mapsTo i F)) hm (2 * p)
  exact ConcreteCategory.congr_hom h _

theorem schemeClosedRelativeGenerator_pullback_support
    (x : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint Y F d)
    [Nonempty (Open.SupportRestriction.BundleCycles.openSupportPullback i.left (irreducibleSetEquivPoints.symm x.val.val))]
    (z : OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d)
    (hz : (irreducibleSetEquivPoints.symm z.val.val : Set X.left) =
      i.left ⁻¹' (irreducibleSetEquivPoints.symm x.val.val : Set Y.left)) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)
      (schemeClosedPullback_mapsTo i F) (2 * p) (OpenSupportedCycle.BundleCycles.schemeClosedRelativeGenerator Y F d p hd x) =
    OpenSupportedCycle.BundleCycles.schemeClosedRelativeGenerator X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d p
      (GradedOpenClass.BundleCycles.openOverGraded_codimension i d p hd) z := by
  rw [schemeClosedRelativeGenerator_pullback_expansion]
  have hc := SchemeCycle.PreimageSupport.BundleCycles.schemeSupportedCycleClass_open_of_support i (irreducibleSetEquivPoints.symm x.val.val)
    (irreducibleSetEquivPoints.symm z.val.val) hz p
    ((congrArg (fun n => n + p) x.val.property).trans hd)
    ((congrArg (fun n => n + p) z.val.property).trans (GradedOpenClass.BundleCycles.openOverGraded_codimension i d p hd))
  let hzi := OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_mapsTo X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' F) d z
  let hzj := SchemeCycle.PreimageSupport.BundleCycles.schemeSupportPreimage_mapsTo i (irreducibleSetEquivPoints.symm x.val.val)
    (irreducibleSetEquivPoints.symm z.val.val) hz
  have h := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i) hzi hzj (2 * p)
  have he := CycleClass.Thom.ThomOpenRestriction.Constructions.pairMap_congr
    (Category.id_comp (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i)) (hzj.comp hzi)
    ((OpenSupportedCycle.BundleCycles.schemeClosedSupportedPoint_mapsTo Y F d x).comp (schemeClosedPullback_mapsTo i F)) (2 * p)
  have heval := ConcreteCategory.congr_hom (h.trans he)
    (SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y (irreducibleSetEquivPoints.symm x.val.val) p
      ((congrArg (fun n => n + p) x.val.property).trans hd))
  exact heval.symm.trans (congrArg
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hzi (2 * p)) hc)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ClosedClassPullbackGenerator.BundleCycles
