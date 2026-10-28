import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedImageGenerator
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.OpenSupportedCycle

/-! # Supported Cycle Gysin -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedCycleGysin.BundleCycles

noncomputable section

/-! Supported Gysin sends the canonical class of every finite supported cycle to the canonical class of its actual full closed-immersion pushforward. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
  (hv : IsOpen (Set.range v)ᶜ) (d r q : ℕ)
  (hr : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + r = Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (hd : d + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i r hr).regularComplementInclusion)ᶜ) (2 * r))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * r) a = (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i r hr).regularThomClass)

theorem closedSupportedCycle_gysin
    (c : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d) :
    (CycleClass.Thom.Intersection.Gysin.Constructions.intersectionGysinIso (q := q) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i r hr) a ha v hv).hom
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d q hd c) =
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v) d (r + q)
      (SupportedImageGenerator.BundleCycles.closedSupportedImage_codimension d r q hr hd) (SupportedImageCycle.BundleCycles.closedSupportedImageCycle i v d c) := by
  classical
  let K : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v)ᶜ (2 * q) →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
        (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v)ᶜ (2 * (r + q)) :=
    (CycleClass.Thom.Intersection.Gysin.Constructions.intersectionGysinIso (q := q) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i r hr) a ha v hv).hom.hom
  change K (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d q hd c) = _
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c e hc he => simp only [map_add, hc, he]
  | single x t =>
    rw [SupportedImageCycle.BundleCycles.closedSupportedImageCycle_single, Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap_single,
      Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap_single, map_smul]
    exact congrArg (fun b => t • b) (SupportedImageGenerator.BundleCycles.closedSupportedImageGenerator_gysin i v hv d r q hr hd a ha x)

theorem closedSupportedCycle_gysin_eq_fullPush
    (c : Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d) :
    (CycleClass.Thom.Intersection.Gysin.Constructions.intersectionGysinIso (q := q) (CycleClass.Thom.Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i r hr) a ha v hv).hom
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d q hd c) =
    Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v) d (r + q)
      (SupportedImageGenerator.BundleCycles.closedSupportedImage_codimension d r q hr hd)
      (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRestrictCycle Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v) d
        (Finite.GradedOverPushforward.BundleCycles.finiteOverGradedPushforward i d (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedSupportedCycle_forget X
          (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range v) d c))) :=
  (closedSupportedCycle_gysin i v hv d r q hr hd a ha c).trans
    (Scheme.OpenSupportedCycle.BundleCycles.schemeClosedRelativeClassMap_eq_of_forget_eq Y (Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) ∩ Set.range v) d
      (r + q) (SupportedImageGenerator.BundleCycles.closedSupportedImage_codimension d r q hr hd) (SupportedImageCycle.BundleCycles.closedSupportedImageCycle i v d c) _
      (SupportedImageCycle.BundleCycles.closedSupportedImageCycle_forget i v d c))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedCycleGysin.BundleCycles
