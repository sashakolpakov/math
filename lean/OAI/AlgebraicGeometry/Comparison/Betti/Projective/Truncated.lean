import OAI.AlgebraicGeometry.Comparison.Betti.BrutalConcreteDerived
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.GodementCechAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Presentation
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CechHypercohomology

/-! # Truncated -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.Truncated

noncomputable section

/-! The actual algebraic-to-holomorphic comparison is bijective on every independently truncated projective de Rham complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.BrutalConcreteDerived.Hodge OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def algebraicHolomorphicTruncatedCohomologyMap (r n : ℤ) :=
  FlasqueDerived.directImageCohomologyMap (Analytification.Base.analytificationMap X)
    ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Algebraic.Sheaves.algebraicDeRhamSheafComplex X) r).extend (ComplexShape.embeddingUpIntGE 0))
    ((Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X) r).extend (ComplexShape.embeddingUpIntGE 0))
    (ImageExtensionSquare.extendDirectImageComplexMap (Analytification.Base.analytificationMap X)
      (BrutalCechAcyclicity.Hodge.brutalSheafDirectImageMap (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) r)) n

theorem projectivePresentation_truncatedComparison_bijective
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (r n : ℤ) :
    Function.Bijective (algebraicHolomorphicTruncatedCohomologyMap X r n) := by
  have hP : IsProper X.hom := P.isProper
  obtain ⟨m, f, hf, hAff, hCover, _, hHol⟩ := Presentation.projectivePresentation_exists_originalCechData X P
  let U := fun i => f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (m + 1) i
  have hClosed : IsClosedImmersion f.left := hf
  have hColumns (q : ℕ) :
      QuasiIso ((Sheaf.CechPullbackTotal.sheafCechPullbackBicomplexMap (Analytification.Base.analytificationMap X) U
        (Godement.AdditiveImage.additiveDirectImageComplexMap (Analytification.Base.analytificationMap X) (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X))).f q) :=
    EmbeddedReferenceForm.embeddedOriginalFormCechMap_quasiIso m X f q
  exact BrutalConcreteDerived.Hodge.brutal_directImageCohomologyMap_bijective (Analytification.Base.analytificationMap X) U
    (Algebraic.Sheaves.algebraicDeRhamSheafComplex X) (Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X)
    (Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X) r hCover (Holomorphic.CechHypercohomology.embeddedAnalyticCoordinateCover_covers X (m + 1) f)
    (Algebraic.GodementCechAcyclicity.algebraicGodementCechIntersectionsAcyclic X U hAff) hHol hColumns n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.Truncated
