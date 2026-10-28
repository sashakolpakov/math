import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveSerreVanishing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingSectionsFinite

/-! # Serre Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.SerreVanishing

noncomputable section

/-! Uniform Serre vanishing for the actual relative hyperplane bundle on every closed projective embedding over a Noetherian affine spectrum. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem relativeEmbedding_tensorTwistingPowers_eventually_vanish
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {X : Over (Spec (.of R))}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of R)) n) [IsClosedImmersion i.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d → ∀ q : ℕ,
      IsZero ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) (q + 1)).obj
        (Tensor.ProductSheaf.tensorModule M (((TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of R)) n).pullback i.left).tensorPower d).sheaf)) := by
  obtain ⟨B, hB⟩ := Closed.ProjectiveSerreVanishing.ClosedProjectiveEmbedding.tensorTwistingPowers_eventually_vanish
    (TwistingSectionsFinite.relativeEmbeddingAffineMap i) M
  refine ⟨B, fun d hd q ↦ ?_⟩
  let E := Tensor.ProductSheaf.tensorModuleCongr (Iso.refl M)
    ((TensorPower.Maps.tensorPowerFunctor X.left d).mapIso (TwistingSectionsFinite.relativeEmbeddingAffineTwistingIso i))
  exact (hB d hd q).of_iso
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) (q + 1)).mapIso E).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.SerreVanishing
