import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberClassPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedClassForget

/-! # Fiber Ordinary Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberOrdinaryClass.BundleCycles

noncomputable section

/-! Ordinary pullback to a genuine smooth principal fiber is the canonical class of the full existing Cartier fiber cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (s : Γ(Y.left, ⊤))
  (d p : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint Y.hom (d + 1))
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

omit [AlgebraicGeometry.IsIntegral Y.left] [Smooth Y.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem principalFiberSupportedClass_forget :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y (irreducibleSetEquivPoints.symm x.val)))ᶜ (2 * p)
      (FiberSupportedGysin.BundleCycles.principalFiberSupportedClass i s d p x hd) =
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p hd (FiberOverCycle.BundleCycles.principalFiberOverCycle i s d x) :=
  (Closed.SupportedClassForget.BundleCycles.schemeClosedRelativeClassMap_forget X _ d p hd (FiberSupportedCycle.BundleCycles.principalFiberSupportedCycle i s d x)).trans
    (congrArg (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p hd) (FiberSupportedCycle.BundleCycles.principalFiberSupportedCycle_forget i s d x))

variable (hzero : Set.range i.left = (Y.left.basicOpen s : Set Y.left)ᶜ)
  (hi : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + 1 = Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (hlocal : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ∃ (U : Y.left.Opens), IsAffineOpen U ∧
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x ∈ CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen Y U ∧
    RingHom.ker (i.left.app U).hom = Ideal.span {Y.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s})

include hzero hlocal in
theorem principalFiber_absoluteClass_pullback
    (hs : CartierCycle.BundleCycles.supportRegularFunction s (irreducibleSetEquivPoints.symm x.val) ≠ 0) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) i
      (Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y (irreducibleSetEquivPoints.symm x.val) p
        (FiberClassPullback.BundleCycles.principalFiberParent_codimension hi d p x hd)) =
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p hd (FiberOverCycle.BundleCycles.principalFiberOverCycle i s d x) := by
  let W := irreducibleSetEquivPoints.symm x.val
  let F := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W)
  let hp := FiberClassPullback.BundleCycles.principalFiberParent_codimension hi d p x hd
  have hm : Set.MapsTo (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i) Fᶜ (Set.range (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportInclusion Y W))ᶜ := fun _ hx => hx
  have hn := ConcreteCategory.congr_hom
    (CycleClass.Geometric.RelativeCohomologyExtensionNaturality.Cohomology.relativeCohomologyInclusion_naturality (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map i) hm (2 * p))
    (Scheme.SupportedCycleClass.BundleCycles.schemeSupportedCycleClass Y W p hp)
  have hc := congrArg (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) Fᶜ (2 * p))
    (FiberClassPullback.BundleCycles.principalFiberSupportedClass_eq_pullback i s hzero hi hlocal d p x hd hs)
  exact hn.symm.trans (hc.trans (principalFiberSupportedClass_forget i s d p x hd))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberOrdinaryClass.BundleCycles
