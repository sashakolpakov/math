import OAI.AlgebraicGeometry.Comparison.Betti.Godement.CechImage
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.GodementCechAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Presentation
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CechHypercohomology

/-! # Reference Godement -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ReferenceGodement

noncomputable section

/-! Projective comparison on global Godement resolutions uses the original algebraic-to-holomorphic coefficient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.Godement.CechImage

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def originalHolomorphicGodementGlobalMap :=
  Sheaf.CechPullbackTotal.topGlobalSectionsPullback (Analytification.Base.analytificationMap X)
    (Godement.AdditiveImage.additiveDirectImageComplexMap (Analytification.Base.analytificationMap X)
      (Godement.PushforwardBicomplex.godementDirectImageTotalMap (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X)))

theorem originalHolomorphicCechTotalMap_eq_sheaf {ι : Type} (U : ι → X.left.Opens) :
    ReferenceFormCechTotal.originalHolomorphicCechTotalMap X U =
      Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap (Analytification.Base.analytificationMap X) U
        (Godement.AdditiveImage.additiveDirectImageComplexMap (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X)) := rfl

theorem originalHolomorphicGodementGlobalMap_quasiIso_of_cover [IsSeparated X.hom]
    {ι : Type} [Finite ι] (U : ι → X.left.Opens)
    (hUaff : ∀ i, IsAffineOpen (U i)) (hU : iSup U = ⊤)
    (hL : ∀ r, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i)) (EmbeddedHolomorphicAcyclicity.nativeHolomorphicFormAdditiveSheaf X r))
    (hα : QuasiIso (ReferenceFormCechTotal.originalHolomorphicCechTotalMap X U)) :
    QuasiIso (originalHolomorphicGodementGlobalMap X) := by
  have hV : (⨆ i, (Opens.map (Analytification.Base.analytificationMap X)).obj (U i)) = ⊤ :=
    (Opens.map_iSup (Analytification.Base.analytificationMap X) U).symm.trans
      (congrArg (Opens.map (Analytification.Base.analytificationMap X)).obj hU)
  exact Godement.CechImage.godementDirectImageTotalMap_global_quasiIso (Analytification.Base.analytificationMap X) U
    (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) hU hV
    (Algebraic.GodementCechAcyclicity.algebraicGodementCechIntersectionsAcyclic X U hUaff) hL hα

theorem projectivePresentation_originalHolomorphicGodementGlobalMap_quasiIso
    [IsSeparated X.hom] (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) :
    QuasiIso (originalHolomorphicGodementGlobalMap X) := by
  obtain ⟨n, f, _, hAff, hCover, hCech, hAcyclic⟩ :=
    Projective.Presentation.projectivePresentation_exists_originalCechData X P
  exact originalHolomorphicGodementGlobalMap_quasiIso_of_cover X
    (fun i => f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (n + 1) i) hAff hCover hAcyclic hCech

end

end OAI.AlgebraicGeometry.Comparison.Betti.ReferenceGodement
