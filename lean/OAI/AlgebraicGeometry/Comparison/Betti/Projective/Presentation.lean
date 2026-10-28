import OAI.AlgebraicGeometry.Comparison.Betti.PositiveProjectiveAmbient
import OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedHolomorphicAcyclicity

/-! # Presentation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.Presentation

noncomputable section

/-! Every smooth integral projective presentation has a genuine finite affine cover with the original de Rham Čech comparison and independent holomorphic form acyclicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectivePresentationCoherentGlobalSectionsMap_isIso
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (M : X.left.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    IsIso (Closed.AnalytificationPushforwardAdditiveSquare.moduleAnalytificationGlobalSectionsMap X M) := by
  obtain ⟨n, i, hi, hg⟩ := PositiveProjectiveAmbient.exists_positive_projective_embedding P
  let f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1)) := Over.homMk i hg
  have : IsClosedImmersion f.left := hi
  exact EmbeddedCoherentGlobal.embeddedCoherentGlobalSectionsMap_isIso n X f M

theorem projectivePresentation_exists_originalCechData
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) :
    ∃ (n : ℕ) (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))),
      IsClosedImmersion f.left ∧
      (∀ i, IsAffineOpen (f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)) ∧
      (⨆ i, f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i) = ⊤ ∧
      QuasiIso (ReferenceFormCechTotal.originalHolomorphicCechTotalMap X
        (fun i => f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i)) ∧
      (∀ r, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (fun i => Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i))
        (EmbeddedHolomorphicAcyclicity.nativeHolomorphicFormAdditiveSheaf X r)) := by
  obtain ⟨n, i, hi, hg⟩ := PositiveProjectiveAmbient.exists_positive_projective_embedding P
  let f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1)) := Over.homMk i hg
  have : IsClosedImmersion f.left := hi
  exact ⟨n, f, hi, EmbeddedHolomorphicAcyclicity.embeddedProjectiveCoordinateCover_affine (n + 1) X f,
    EmbeddedHolomorphicAcyclicity.embeddedProjectiveCoordinateCover_covers (n + 1) X f,
    EmbeddedReferenceForm.embeddedOriginalHolomorphicCechTotalMap_quasiIso n X f,
    EmbeddedHolomorphicAcyclicity.embeddedHolomorphicFormsCechAcyclic (n + 1) X f⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.Presentation
