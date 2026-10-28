import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwists
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoherentGlobalGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ModuleZeroCriterion

/-! # Projective Global Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveGlobalGeneration.ClosedProjectiveEmbedding

noncomputable section

/-! Sufficiently positive powers of the actual restricted hyperplane bundle globally generate every coherent sheaf on a closed projective embedding. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem tensorTwistingPowers_eventually_hasFiniteGlobalGenerators
    {R : Type u} [CommRing R] {n : ℕ} {X : Over (Spec (.of R))}
    (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion i.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators
      (Tensor.ProductSheaf.tensorModule M (((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback i.left).tensorPower d).sheaf) := by
  let J := ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i
  let e : Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J) ⟶ X.left := (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom.left
  have : IsIso e := (Over.forget _).map_isIso (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom
  let N : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J)).Modules := (Scheme.Modules.pullback e).obj M
  have hNq : N.IsQuasicoherent := Quasicoherent.PullbackIsoFiniteness.module_openPullback_quasicoherent e M
  have hNt : N.IsFiniteType := Quasicoherent.PullbackIsoFiniteness.module_openPullback_finiteType e M
  obtain ⟨B, hB⟩ := @Projective.CoherentGlobalGeneration.projective_finiteType_eventually_hasFiniteGlobalGenerators R _ n J N hNq hNt
  refine ⟨B, fun d hd => ?_⟩
  apply Finite.GlobalModuleGenerators.HasFiniteGlobalGenerators.of_pullback_iso e
  exact (hB d hd).of_iso (Projective.PresentationTensorTwists.ClosedProjectiveEmbedding.tensorTwistPullbackIso i M d).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveGlobalGeneration.ClosedProjectiveEmbedding
