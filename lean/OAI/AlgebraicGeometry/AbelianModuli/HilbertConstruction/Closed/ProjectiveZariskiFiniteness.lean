import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardZariskiComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.BaseCongruence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ZariskiCohomologyFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageType

/-! # Projective Zariski Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveZariskiFiniteness

noncomputable section

/-! Genuine cohomology of a coherent sheaf on any closed projective embedding over a Noetherian affine base is finite in every degree. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem ClosedProjectiveEmbedding.cohomology_finite {n : ℕ} {X : Over (Spec (.of R))}
    (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion i.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) q).obj M) := by
  cases q with
  | zero =>
      have : Module.Finite R ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom)).obj M) :=
        ProjectiveCoherentSectionFiniteness.ClosedProjectiveEmbedding.coherentSections_finite i M
      exact Module.Finite.equiv (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv _ M).symm
  | succ q =>
      let e := ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i
      let J := ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i
      let f : X.left ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J) := e.inv.left
      have : IsIso f := (Over.forget _).map_isIso e.inv
      let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)
      let c := Coefficient.ModulePresheaf.schemeCoefficientMap p
      let : IsProper p := HilbertScheme.Presentations.Projective.Properness.GradedHilbert.projectiveQuotient_proper J
      let : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)).IsSeparated := ⟨by
        rw [← terminal.comp_from p]
        infer_instance⟩
      let N : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)).Modules := (Scheme.Modules.pushforward f).obj M
      have hNq : N.IsQuasicoherent := Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f M
      have hNt : N.IsFiniteType := HilbertConstruction.Finite.ImageType.finite_directImage_finiteType f M
      have hf : Module.Finite R ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor c (q + 1)).obj N) :=
        @Projective.ZariskiCohomologyFiniteness.ZariskiCohomology.projective_zariski_cohomology_finite R _ _ n J N hNq hNt (q + 1)
      have hc : f.appTop.hom.comp c = Coefficient.ModulePresheaf.schemeCoefficientMap X.hom :=
        (Coefficient.GlobalSectionsPushforward.schemeCoefficientMap_comp f p).symm.trans (congrArg Coefficient.ModulePresheaf.schemeCoefficientMap e.inv.w)
      let E := (CoefficientCohomology.BaseCongruence.ZariskiCohomology.coefficientCohomologyCongr hc M (q + 1)).symm ≪≫
        Affine.PushforwardZariskiComparison.affineCover_pushforward_cohomologyIso f c M (Projective.CechCover.projectiveCechOpens J)
          (Projective.CechZariskiComparison.projectiveCechOpens_iSup J) (Projective.CechCover.projectiveCechOpens_affine J) q
      exact @Module.Finite.equiv R _ _ _ _ _ _ _ hf E.symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveZariskiFiniteness
