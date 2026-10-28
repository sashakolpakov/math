import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberOrdinaryClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.SectionNonzero

/-! # Fiber Open Cycle Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberOpenCycleClass.BundleCycles

noncomputable section

/-! The principal-fiber comparison extends to every finite cycle closed from an actual section-nonvanishing open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left] (s : Γ(Y.left, ⊤))
  (hzero : Set.range i.left = (Y.left.basicOpen s : Set Y.left)ᶜ)
  (hi : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + 1 = Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (hlocal : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ∃ (U : Y.left.Opens), IsAffineOpen U ∧
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x ∈ CycleClass.Thom.Scheme.SectionEvaluation.Constructions.analyticOpen Y U ∧
    RingHom.ker (i.left.app U).hom = Ideal.span {Y.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s})
  {U : Scheme} [AlgebraicGeometry.IsNoetherian U] (j : U ⟶ Y.left) [IsOpenImmersion j]
  (hj : Set.range j ⊆ Y.left.basicOpen s) (d p : ℕ)
  (hd : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)

include hi hd in
omit [AlgebraicGeometry.IsNoetherian X.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem principalFiberClosure_codimension : (d + 1) + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by
  have h := Closed.SupportedImageGenerator.BundleCycles.closedSupportedImage_codimension d 1 p hi hd
  omega

include hzero hlocal hj in
theorem principalFiber_absoluteClass_openExtension
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ Y.hom) (d + 1) →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) i
      (LineBundles.Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass Y (d + 1) p (principalFiberClosure_codimension hi d p hd)
        (Open.CycleRestriction.BundleCycles.openDimensionCycleExtension j Y.hom (d + 1) c)) =
    LineBundles.Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p hd
      (DimensionChow.BundleCycles.dimensionCycleTransport i.w d (CartierFiber.BundleCycles.principalCartierFiberCycleMap i.left s Y.hom d
        (Open.CycleRestriction.BundleCycles.openDimensionCycleExtension j Y.hom (d + 1) c))) := by
  classical
  let K : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Y (2 * p) →ₗ[ℚ] Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X (2 * p) :=
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) i).hom
  change K (LineBundles.Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass Y (d + 1) p (principalFiberClosure_codimension hi d p hd)
    (Open.CycleRestriction.BundleCycles.openDimensionCycleExtension j Y.hom (d + 1) c)) = _
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c e hc he => simp only [map_add, hc, he]
  | single x r =>
    let y := Open.CycleRestriction.BundleCycles.openDimensionPointEmbedding j Y.hom (d + 1) x
    have hcl : Open.CycleRestriction.BundleCycles.openDimensionCycleExtension j Y.hom (d + 1) (Finsupp.single x r) = Finsupp.single y r :=
      Finsupp.mapDomain_single
    have hpcl : CartierFiber.BundleCycles.principalCartierFiberCycleMap i.left s Y.hom d (Finsupp.single y r) =
        r • CartierFiber.BundleCycles.principalCartierFiberCycle i.left s Y.hom d y := Finsupp.linearCombination_single ℚ r y
    rw [hcl, hpcl, LineBundles.Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_single, map_smul, map_smul, map_smul]
    exact congrArg (fun b => r • b)
      (FiberOrdinaryClass.BundleCycles.principalFiber_absoluteClass_pullback i s d p y hd hzero hi hlocal
        (Support.SectionNonzero.BundleCycles.supportRegularFunction_pointClosure_ne_zero j s hj x.val))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.FiberOpenCycleClass.BundleCycles
