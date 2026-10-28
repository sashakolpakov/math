import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveGenerationBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.RankCommonOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChartsPullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.BasisSourceCharts

/-! # Projective Chart Generation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveChartGeneration.BundleCycles

noncomputable section

/-! A genuine base-changed finite free infinity chart generates
all its Chow classes with the rank inherited from the global projection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian U] [E.IsSeparated] [U.IsSeparated]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Fintype ι]
    (basis : Module.Basis ι R M)
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    (b : U ⟶ Spec (.of R)) (i : U ⟶ X) [IsOpenImmersion i]
    (j : pullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b ⟶ E) [IsOpenImmersion j]
    (hs : IsPullback (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b) j i p)
    (e : (L.pullback j).sheaf ≅ ((SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback
      (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b)).sheaf)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)
    (u : U)

omit [AlgebraicGeometry.IsNoetherian E] [E.IsSeparated] [Smooth p] in
include basis e u in
theorem freeProjectiveChart_chow_generated (d : ℕ)
    (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b ≫ (i ≫ f)) d) :
    α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b) (i ≫ f) r
      (hp.of_isPullback _ i j hs) (L.pullback j) d := by
  have hq := Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_sourceCharts basis
  have hcard : r = Nat.card ι := AffineSource.RankCommonOpen.BundleCycles.affineSpaceSourceRank_openSquare p
    (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b) i j hs.w f r (Nat.card ι) hp (hq.baseChange b) u
  have hqr : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) r := hcard.symm ▸ hq
  rw [ProjectiveChow.GeneratorsIso.BundleCycles.projectiveChowGenerated_lineBundleIso _ (i ≫ f) r (hp.of_isPullback _ i j hs) e]
  exact ProjectiveGenerationBaseChange.BundleCycles.freeProjectiveChow_baseChange_generated basis b (i ≫ f) r hcard.symm hqr d α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveChartGeneration.BundleCycles
