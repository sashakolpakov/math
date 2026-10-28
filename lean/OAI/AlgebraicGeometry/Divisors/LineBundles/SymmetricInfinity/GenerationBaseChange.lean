import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.GenerationBaseChangeStep
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.IdealRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AugmentedAffineChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Integral

/-! # Generation Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.GenerationBaseChange.BundleCycles

noncomputable section

/-! The actual symmetric infinity hyperplane gives the projective
generation induction step after arbitrary base change. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    {ι : Type} [Fintype ι] (basis : Module.Basis ι R (R × M))
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M)))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M)))]
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (b : Y ⟶ Spec (.of R)) (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hr : Nat.card ι = r + 1)
    (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) (r + 1))
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) r)
    (hgen : ∀ d (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b ≫ f) d),
      α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b) f r
        (hq.baseChange b) ((Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback
          (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b)) d)

include basis hr hgen in
theorem symmetricInfinityChow_generation_baseChange_step (d : ℕ)
    (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) b ≫ f) d) :
    α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) b) f (r + 1)
      (hp.baseChange b) ((Bundle.Cycles.symmetricInfinityIdealLineBundle R (R × M)).pullback
        (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) b)) d :=
  Projective.GenerationBaseChangeStep.BundleCycles.projectiveChowGeneration_baseChange_step (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M)))
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) (Inclusion.BundleCycles.symmetricInfinityInclusion R (R × M))
    (SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd R R (R × M)) _)
    (Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R (R × M)) b f r hp hq
    (Bundle.Cycles.symmetricInfinityIdealLineBundle R M) (IdealRestriction.BundleCycles.symmetricInfinityIdealRestrictionIso R M) ι hr
    (Symmetric.AugmentedAffineChart.BundleCycles.symmetricAugmentedAffineChart basis) (Symmetric.AugmentedAffineChart.BundleCycles.symmetricAugmentedAffineChart_over basis)
    (Symmetric.AugmentedAffineChart.BundleCycles.symmetricAugmentedAffineChart_complement basis) hgen d α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.GenerationBaseChange.BundleCycles
