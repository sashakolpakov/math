import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwists
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ZariskiSerreVanishing

/-! # Projective Serre Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveSerreVanishing.ClosedProjectiveEmbedding

noncomputable section

/-! Serre vanishing for actual powers of the restricted hyperplane bundle on an arbitrary closed projective embedding. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem tensorTwistingPowers_eventually_vanish {R : Type u} [CommRing R] [IsNoetherianRing R]
    {n : ℕ} {X : Over (Spec (.of R))}
    (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion i.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ q : ℕ,
      IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) (q + 1)).obj
        (Tensor.ProductSheaf.tensorModule M (((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback i.left).tensorPower d).sheaf)) := by
  let J := ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i
  let e : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J) ⟶ X.left := (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom.left
  have : IsIso e := (Over.forget _).map_isIso (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom
  let N : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)).Modules := (Scheme.Modules.pullback e).obj M
  have hNq : N.IsQuasicoherent := Quasicoherent.PullbackIsoFiniteness.module_openPullback_quasicoherent e M
  have hNt : N.IsFiniteType := Quasicoherent.PullbackIsoFiniteness.module_openPullback_finiteType e M
  obtain ⟨B, hB⟩ := @Projective.ZariskiSerreVanishing.ZariskiCohomology.projective_zariski_Serre_vanishing R _ _ n J N hNq hNt
  refine ⟨B, fun d hd q ↦ ?_⟩
  let L := ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback i.left).tensorPower d
  have : (Tensor.ProductSheaf.tensorModule M L.sheaf).IsQuasicoherent := LineBundle.TensorCoherence.tensorModuleRight_lineBundle_quasicoherent M L
  exact (hB d hd q).of_iso (Projective.PresentationCohomologyPullback.ClosedProjectiveEmbedding.cohomologyPullbackIso i (Tensor.ProductSheaf.tensorModule M L.sheaf) q ≪≫
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J))) (q + 1)).mapIso
        (Projective.PresentationTensorTwists.ClosedProjectiveEmbedding.tensorTwistPullbackIso i M d))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveSerreVanishing.ClosedProjectiveEmbedding
