import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.LineBundleEulerPolynomial

/-! # Twisted Line -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Euler polynomiality holds after any fixed line-bundle twist, using the
same global finite-difference identity on line-bundle classes. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem TwistedLine.lineBundleEulerShift_power_eval_class {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) (q : Line.Bundles.LineBundle.IsoClass X) (n : ℕ) :
    ((LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf L)) ^ n) (LineBundle.EulerShifts.lineBundleClassEuler p) q =
      LineBundle.EulerShifts.lineBundleClassEuler p (q * Line.Bundles.LineBundle.classOf L ^ n) := by
  rw [← (LineBundle.EulerShifts.lineBundleEulerShift X).map_pow]
  rfl

theorem TwistedLine.lineBundleClassEuler_polynomial_of_two_generated
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsProper p]
    (L H : Line.Bundles.LineBundle X) (hH : Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators H.sheaf)
    (hLH : Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators (L.tensor H).sheaf) (q : Line.Bundles.LineBundle.IsoClass X) :
    ∃ P : Polynomial ℚ, ∀ n : ℕ,
      P.eval (n : ℚ) = (LineBundle.EulerShifts.lineBundleClassEuler p (q * Line.Bundles.LineBundle.classOf L ^ n) : ℚ) := by
  obtain ⟨r, hr⟩ := KoszulEulerDifference.lineBundleEulerShift_difference_annihilates_of_generators p H hH
  obtain ⟨s, hs⟩ := KoszulEulerDifference.lineBundleEulerShift_difference_annihilates_of_generators p (L.tensor H) hLH
  let T := LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf L)
  let U := LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf H)
  let v := LineBundle.EulerShifts.lineBundleClassEuler p
  have hTUv : ((T * U - 1) ^ s) v = 0 := by
    change ((LineBundle.EulerShifts.lineBundleEulerShift X (Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf H) - 1) ^ s)
      (LineBundle.EulerShifts.lineBundleClassEuler p) = 0 at hs
    rwa [(LineBundle.EulerShifts.lineBundleEulerShift X).map_mul] at hs
  have hv := CommutingDifferenceAnnihilation.commuting_tensor_differences_annihilate T U
    (LineBundle.EulerShifts.lineBundleEulerShift_commute X (Line.Bundles.LineBundle.classOf L) (Line.Bundles.LineBundle.classOf H)) v s r hTUv hr
  let φ : (Line.Bundles.LineBundle.IsoClass X → ℤ) →+ ℤ :=
    { toFun := fun f => f q, map_zero' := rfl, map_add' := fun _ _ => rfl }
  obtain ⟨P, hP⟩ := EndomorphismOrbitPolynomial.exists_polynomial_of_endomorphism_difference_annihilates T φ v (s + r) hv
  refine ⟨P, fun n => ?_⟩
  exact (hP n).trans (congrArg (fun z : ℤ => (z : ℚ)) (TwistedLine.lineBundleEulerShift_power_eval_class p L q n))

theorem TwistedLine.lineBundleClassEuler_polynomial_of_projectiveIso
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p]
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n)) (e : X ≅ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (L : Line.Bundles.LineBundle X) (q : Line.Bundles.LineBundle.IsoClass X) :
    ∃ P : Polynomial ℚ, ∀ m : ℕ,
      P.eval (m : ℚ) = (LineBundle.EulerShifts.lineBundleClassEuler p (q * Line.Bundles.LineBundle.classOf L ^ m) : ℚ) := by
  obtain ⟨H, hH, hLH⟩ := Projective.IsoGeneratedFactors.lineBundle_two_generated_factors_of_projectiveIso I e L
  exact TwistedLine.lineBundleClassEuler_polynomial_of_two_generated p L H hH hLH q

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.lineBundleClass_eulerPolynomial
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (M : Line.Bundles.LineBundle X)
    (q : Line.Bundles.LineBundle.IsoClass X) :
    ∃ P : Polynomial ℚ, ∀ n : ℕ,
      P.eval (n : ℚ) = (LineBundle.EulerShifts.lineBundleClassEuler p (q * Line.Bundles.LineBundle.classOf M ^ n) : ℚ) := by
  have : IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism p E.sections E.covers).left := E.closedImmersion
  have : Flat (Over.mk p).hom := inferInstanceAs (Flat p)
  have : LocallyOfFinitePresentation (Over.mk p).hom := inferInstanceAs (LocallyOfFinitePresentation p)
  obtain ⟨I, ⟨e⟩⟩ := Relative.EmbeddingProjectiveQuotient.relativeEmbedding_has_projectiveQuotient_iso
    (SectionsProjectiveMorphism.sectionProjectiveMorphism p E.sections E.covers)
  exact TwistedLine.lineBundleClassEuler_polynomial_of_projectiveIso p I e M q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
