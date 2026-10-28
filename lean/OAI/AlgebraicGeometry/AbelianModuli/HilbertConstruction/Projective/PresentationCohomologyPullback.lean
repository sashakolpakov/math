import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveZariskiFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InversePushforwardPullback

/-! # Presentation Cohomology Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationCohomologyPullback.ClosedProjectiveEmbedding

noncomputable section

/-! The homogeneous presentation of a closed projective embedding preserves genuine coefficient cohomology under module pullback. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def cohomologyPullbackIso {R : Type u} [CommRing R] {n : ℕ} {X : Over (Spec (.of R))}
    (i : X ⟶ ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion i.left]
    (M : X.left.Modules) [M.IsQuasicoherent] (q : ℕ) :
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) (q + 1)).obj M ≅
      (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i)))) (q + 1)).obj
          ((Scheme.Modules.pullback (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom.left).obj M) := by
  let J := Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i
  let e : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J) ≅ X.left := (Over.forget _).mapIso (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i)
  let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap p
  let : IsProper p := HilbertScheme.Presentations.Projective.Properness.GradedHilbert.projectiveQuotient_proper J
  let : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)).IsSeparated := ⟨by
    rw [← terminal.comp_from p]
    infer_instance⟩
  have hc : e.inv.appTop.hom.comp c = Coefficient.ModulePresheaf.schemeCoefficientMap X.hom :=
    (Coefficient.GlobalSectionsPushforward.schemeCoefficientMap_comp e.inv p).symm.trans
      (congrArg Coefficient.ModulePresheaf.schemeCoefficientMap (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).inv.w)
  exact (CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr hc M (q + 1)).symm ≪≫
    Affine.PushforwardZariskiComparison.affineCover_pushforward_cohomologyIso e.inv c M (CechCover.projectiveCechOpens J)
      (CechZariskiComparison.projectiveCechOpens_iSup J) (CechCover.projectiveCechOpens_affine J) q ≪≫
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).mapIso
      (Module.InversePushforwardPullback.moduleInversePushforwardPullbackIso e M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationCohomologyPullback.ClosedProjectiveEmbedding
