import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.CycleTrace
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.CompactTraceDetection

/-! # Cycle Class Zero -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.CycleClassZero.BundleCycles

noncomputable section

/-! Finite morphisms preserve vanishing of the canonical class of a
finite cycle, with all actual residue-field degrees in its image cycle. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (f : X ⟶ Y) [IsFinite f.left] {I : Type} [Fintype I] (Z : I → IrreducibleCloseds X.left)

def finiteCycleOmittedBoundary : Closeds Y.left :=
  ⟨⋃ i, (FiniteSupport.Cover.BundleCycles.finiteSupportOmittedBoundary f (Z i) : Set Y.left),
    isClosed_iUnion_of_finite (fun i => (FiniteSupport.Cover.BundleCycles.finiteSupportOmittedBoundary f (Z i)).isClosed)⟩

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem finiteCycleOmittedBoundary_codimension (q : ℕ)
    (hB : ∀ i, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f (Z i)) Y.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (A : IrreducibleCloseds Y.left) (hA : (A : Set Y.left) ⊆ finiteCycleOmittedBoundary f Z) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension A Y.hom + (q + 1) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by
  have hη := A.isIrreducible.isGenericPoint_genericPoint A.isClosed
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hA hη.mem)
  apply FiniteSupport.Cover.BundleCycles.finiteSupportOmittedBoundary_codimension f (Z i) q (hB i) A
  rw [← hη.def]
  exact closure_minimal (Set.singleton_subset_iff.mpr hi) (FiniteSupport.Cover.BundleCycles.finiteSupportOmittedBoundary f (Z i)).isClosed

omit [AlgebraicGeometry.IsIntegral X.left] [Smooth X.hom] [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [AlgebraicGeometry.IsIntegral Y.left] [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] in
theorem finiteCycleRetainedOpen_subset (i : I) :
    (CycleClass.Thom.ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen Y (finiteCycleOmittedBoundary f Z).compl : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⊆
      FiniteSupport.Cover.BundleCycles.finiteSupportRetainedOpen f (Z i) := by
  intro x hx hbad
  exact hx (Set.mem_iUnion.mpr ⟨i, hbad⟩)

theorem finiteCycleClass_zero_of_source_zero
    (p q : ℕ)
    (hZ : ∀ i, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z i) X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hB : ∀ i, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f (Z i)) Y.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (a : I → ℚ)
    (hzero : ∑ i, a i • Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X (Z i) p (hZ i) = 0)
    (n : ℕ) (hp : 2 * p + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    (hq : 2 * q + n = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) :
    ∑ i, a i • ((f.left.residueDegree (irreducibleSetEquivPoints (Z i)) : ℚ) •
      Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f (Z i)) q (hB i)) = 0 := by
  apply Scheme.CompactTraceDetection.BundleCycles.schemeCohomology_zero_of_compactTrace_outside_closed Y (finiteCycleOmittedBoundary f Z) (q + 1)
    (finiteCycleOmittedBoundary_codimension f Z q hB) (2 * q) n hq (by omega)
  intro L hL b
  let bX := AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)), FiniteSupport.CycleTrace.BundleCycles.finiteSupport_compactPreimage f L⟩ n
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
      (A := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹' (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))ᶜ)
      (B := (L : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))ᶜ) (fun _ hx => hx) n b)
  let sourceEval : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X (2 * p) →ₗ[ℚ] ℚ :=
    (LinearMap.applyₗ' ℚ bX).comp
      (AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
        (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (2 * p) n hp)
  let targetEval : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) Y (2 * q) →ₗ[ℚ] ℚ :=
    (LinearMap.applyₗ' ℚ
      (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) L n b)).comp
      (AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation (Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
        (M := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (2 * q) n hq)
  have hz := congrArg sourceEval hzero
  simp only [map_sum, map_smul, map_zero] at hz
  change targetEval (∑ i, a i • ((f.left.residueDegree (irreducibleSetEquivPoints (Z i)) : ℚ) •
      Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f (Z i)) q (hB i))) = 0
  simp only [map_sum, map_smul]
  refine (Finset.sum_congr rfl ?_).trans hz
  intro i _
  exact congrArg (fun t => a i • t)
    (FiniteSupport.CycleTrace.BundleCycles.finiteSupport_cycle_compactTrace f (Z i) p q (hZ i) (hB i) n hp hq L
      (hL.trans (finiteCycleRetainedOpen_subset f Z i)) b).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.CycleClassZero.BundleCycles
