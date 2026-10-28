import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.AbsoluteOpenPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportGenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteClass

/-! # Empty Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.EmptyPullback.BundleCycles

noncomputable section

/-! A canonical cycle class restricts to zero on an actual open
that misses its support, including every omitted graded generic point. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (f : X ⟶ Y) (B : IrreducibleCloseds Y.left) (p : ℕ)
    (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

theorem schemeAbsoluteCycleClass_pullback_empty
    (hempty : f.left ⁻¹' (B : Set Y.left) = ∅) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) f (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y B p hp) = 0 := by
  let TX := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
  let TY := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
  let A := (∅ : Set TX)ᶜ
  let C := (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y B))ᶜ
  have hm : Set.MapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) A C := by
    intro x _ hx
    rw [CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion_range] at hx
    have h : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ f.left ⁻¹' (B : Set Y.left) := hx
    rw [hempty] at h
    exact h
  let c := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) hm
    (2 * p) (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp)
  have h := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) hm (2 * p))
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y B p hp)
  have hz := (CycleClass.Geometric.ClosedSupportFiltration.Cycles.cohomologyWithEmptySupport_isZero (ModuleCat.of ℚ ℚ) TX (2 * p)).eq_of_src
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) TX A (2 * p)) 0
  exact h.symm.trans ((ConcreteCategory.congr_hom hz c).trans rfl)

theorem schemeCycleClass_pullback_empty
    (hempty : f.left ⁻¹' (B : Set Y.left) = ∅) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f (Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass Y B p hp) = 0 := by
  change Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) f
    (cast (congrArg (fun n => (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Y n : Type)) (two_mul p))
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y B p hp)) = _
  rw [Scheme.AbsoluteProjection.BundleCycles.schemeBettiMap_cast (ModuleCat.of ℚ ℚ) f (two_mul p), schemeAbsoluteCycleClass_pullback_empty f B p hp hempty]
  exact (Scheme.GradedAbsoluteClass.BundleCycles.schemeBettiDegreeEquiv_apply X (two_mul p) 0).symm.trans (map_zero _)

omit [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem openSupport_preimage_empty_of_generic_not_mem [IsOpenImmersion f.left]
    (hB : irreducibleSetEquivPoints B ∉ Set.range f.left) : f.left ⁻¹' (B : Set Y.left) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hB ((Open.SupportGenericPoint.BundleCycles.openSupportPullback_nonempty_generic f.left B).mp
    ((Open.SupportRestriction.BundleCycles.openSupportPullback_nonempty_iff f.left B).mpr ⟨x, hx⟩))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SchemeCycle.EmptyPullback.BundleCycles
