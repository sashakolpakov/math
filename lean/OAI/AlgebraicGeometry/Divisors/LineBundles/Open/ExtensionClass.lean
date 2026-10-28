import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteOpenClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Punctured.Point

/-! # Extension Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ExtensionClass.BundleCycles

noncomputable section

/-! Restricting the class of the closure of an actual finite open cycle recovers its full original class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [AlgebraicGeometry.IsNoetherian X.left]
  (i : X ⟶ Y) [IsOpenImmersion i.left] (d : ℕ)

theorem openOverGradedRestriction_extension
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i.left ≫ Y.hom) d →₀ ℚ) :
    GradedOverRestriction.BundleCycles.openOverGradedRestriction i d (CycleRestriction.BundleCycles.openDimensionCycleExtension i.left Y.hom d c) =
      DimensionChow.BundleCycles.dimensionCycleTransport i.w d c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c e hc he => simp only [map_add, hc, he]
  | single x r =>
    let y : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d := ⟨x.val, by
      rw [← i.w]
      exact x.property⟩
    have hx : CycleRestriction.BundleCycles.openDimensionPointEmbedding i.left Y.hom d x = GradedOverRestriction.BundleCycles.openOverDimensionPointEmbedding i d y :=
      Subtype.ext rfl
    have hc : CycleRestriction.BundleCycles.openDimensionCycleExtension i.left Y.hom d (Finsupp.single x r) =
        Finsupp.single (CycleRestriction.BundleCycles.openDimensionPointEmbedding i.left Y.hom d x) r := Finsupp.mapDomain_single
    rw [hc, hx, GradedOverRestriction.BundleCycles.openOverGradedRestriction_single]
    exact (Punctured.Point.BundleCycles.dimensionCycleTransport_single i.w d x y rfl r).symm

variable [IsIntegral X.left] [Smooth X.hom] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
  [IsIntegral Y.left] [Smooth Y.hom] [AlgebraicGeometry.IsNoetherian Y.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)] (p : ℕ)
  (hY : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)

theorem schemeGradedAbsoluteClass_openExtension
    (c : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i.left ≫ Y.hom) d →₀ ℚ) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (2 * p) i
      (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass Y d p hY (CycleRestriction.BundleCycles.openDimensionCycleExtension i.left Y.hom d c)) =
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p (Scheme.GradedOpenClass.BundleCycles.openOverGraded_codimension i d p hY)
      (DimensionChow.BundleCycles.dimensionCycleTransport i.w d c) := by
  have h := LinearMap.congr_fun (Scheme.GradedAbsoluteOpenClass.BundleCycles.schemeGradedAbsoluteCycleClass_openRestriction i d p hY)
    (CycleRestriction.BundleCycles.openDimensionCycleExtension i.left Y.hom d c)
  exact h.symm.trans (congrArg (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p (Scheme.GradedOpenClass.BundleCycles.openOverGraded_codimension i d p hY))
    (openOverGradedRestriction_extension i d c))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ExtensionClass.BundleCycles
