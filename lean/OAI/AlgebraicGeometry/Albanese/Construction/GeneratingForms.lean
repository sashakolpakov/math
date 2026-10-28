import OAI.AlgebraicGeometry.Albanese.Construction.AnalyticPullback
import OAI.AlgebraicGeometry.Albanese.Construction.ClosedFormDescent
import OAI.AlgebraicGeometry.Albanese.Construction.GeneratingWords

/-! # Generating Forms -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.GeneratingForms

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [ConnectedSpace X.carrier]

/-- The original connected smooth projective presentation is an integral variety. -/
def connectedVariety : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := ⟨X, Construction.Smooth.connected_presentation_integral X⟩

instance connectedOver_integral : IsIntegral X.toOver.left := Construction.Smooth.connected_presentation_integral X
instance connectedOver_smooth : Smooth X.toOver.hom := X.smooth

instance connectedOverPoints_compact : CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  inferInstanceAs (CompactSpace (connectedVariety X).analyticSpace)

instance differenceDomain_integral : IsIntegral (X.toOver ⊗ X.toOver).left :=
  Construction.Smooth.smooth_tensor_integral X.toOver X.toOver

instance differenceDomain_smooth : Smooth (X.toOver ⊗ X.toOver).hom := by
  change Smooth (CategoryTheory.Limits.pullback.fst X.toOver.hom X.toOver.hom ≫ X.toOver.hom)
  infer_instance

instance differencePoints_compact : CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X.toOver ⊗ X.toOver)) :=
  (AbelianVariety.AnalyticGroup.Constructions.ExteriorCohomology.schemePointProductHomeomorph X.toOver X.toOver).symm.compactSpace

/-- Word domains have compact actual analytic point spaces, by the product
homeomorphism and compactness of the fixed source. -/
instance wordPoints_compact (n : ℕ) : CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ImageWords.wordDomain X n)) := by
  induction n with
  | zero =>
    have : Subsingleton (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ImageWords.wordDomain X 0)) :=
      inferInstanceAs (Subsingleton (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase)))
    infer_instance
  | succ n ih =>
    exact (AbelianVariety.AnalyticGroup.Constructions.ExteriorCohomology.schemePointProductHomeomorph (ImageWords.wordDomain X n) (X.toOver ⊗ X.toOver)).symm.compactSpace

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver)
  (form : AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := A.variety.analyticModel) (G := A.variety.analyticSpace) 1)

theorem differenceMap_pullback_zero (ha : AnalyticPullback.nativePullback a 1 form.val = 0) :
    AnalyticPullback.nativePullback (ImageWords.differenceMap X A a) 1 form.val = 0 := by
  apply AnalyticPullback.nativePullback_div_zero A form
  · exact AnalyticPullback.nativePullback_comp_zero (fst X.toOver X.toOver) a 1 form.val ha
  · exact AnalyticPullback.nativePullback_comp_zero (snd X.toOver X.toOver) a 1 form.val ha

/-- If an invariant one-form vanishes on the source map, it also vanishes
on every word of point differences. -/
theorem wordMap_pullback_zero (ha : AnalyticPullback.nativePullback a 1 form.val = 0) (n : ℕ) :
    AnalyticPullback.nativePullback (ImageWords.wordMap X A a n) 1 form.val = 0 := by
  induction n with
  | zero =>
    let _ := ImageWords.wordDomain_integral X 0
    let _ := ImageWords.wordDomain_smooth X 0
    exact AnalyticPullback.nativePullback_one A form.val
  | succ n ih =>
    let _ := ImageWords.wordDomain_integral X (n + 1)
    let _ := ImageWords.wordDomain_smooth X (n + 1)
    let _ := ImageWords.wordDomain_integral X n
    let _ := ImageWords.wordDomain_smooth X n
    apply AnalyticPullback.nativePullback_mul_zero A form
    · exact AnalyticPullback.nativePullback_comp_zero (fst (ImageWords.wordDomain X n) (X.toOver ⊗ X.toOver))
        (ImageWords.wordMap X A a n) 1 form.val ih
    · exact AnalyticPullback.nativePullback_comp_zero (snd (ImageWords.wordDomain X n) (X.toOver ⊗ X.toOver))
        (ImageWords.differenceMap X A a) 1 form.val (differenceMap_pullback_zero X A a form ha)

/-- Generation makes invariant one-forms detectable on the source. The
surjective compact word map is a quotient, and closed-form descent applies. -/
theorem generating_invariantOneForm_pullback_zero
    (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) (hgen : GeneratedClosed.Generates X A a)
    (ha : AnalyticPullback.nativePullback a 1 form.val = 0) : form = 0 := by
  let n := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap
  let w := ImageWords.wordMap X A a n
  have hsurj : Function.Surjective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map w) :=
    GeneratingWords.generating_word_point_surjective X x₀ A a hgen n le_rfl
  have hcont := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map w
  have hquot : Topology.IsQuotientMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map w) :=
    hcont.isClosedMap.isQuotientMap hcont hsurj
  let α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms A.variety.analyticModel A.variety.analyticSpace 1 :=
    ⟨form.val, AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms_closed form.val form.property⟩
  have hα : α = 0 := ClosedFormDescent.closed_oneForm_eq_zero_of_quotient_pullback
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map w) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map w ∞) hquot α
    (wordMap_pullback_zero X A a form ha n)
  apply Subtype.ext
  exact congrArg (fun β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms A.variety.analyticModel A.variety.analyticSpace 1 =>
    β.val) hα

end

end OAI.AlgebraicGeometry.Albanese.Construction.GeneratingForms
