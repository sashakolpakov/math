import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.RankCommonOpen

/-! # Charts Rank From Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ChartsRankFromOpen.BundleCycles

noncomputable section

/-! A constant-rank affine open determines the ranks of every actual
free projective infinity chart of its integral compactification. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E A X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) (q : A ⟶ X) [GeometricallyIntegral p] [GeometricallyIntegral q]
    (j : A ⟶ E) [IsOpenImmersion j] (hj : j ≫ p = q)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (H : ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)

include H hj f hq in
theorem freeInfinityCharts_rank_of_open : InfinityCharts.BundleCycles.HasFreeProjectiveInfinityChartsOfRank p L r := by
  intro x
  obtain ⟨C⟩ := H x
  obtain ⟨u, _⟩ := C.contains
  let : AlgebraicGeometry.IsNoetherian (Spec C.coefficient) := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian C.baseMap
  let : AlgebraicGeometry.IsNoetherian
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme C.coefficient (C.coefficient × C.module)) :=
    Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian C.totalMap
  let : GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase C.coefficient (C.coefficient × C.module)) :=
    Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_geometricallyIntegral C.basis
  have hC : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase C.coefficient (C.coefficient × C.module)) C.rank := by
    simpa only [Nat.card_fin] using Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_sourceCharts C.basis
  exact ⟨C, (AffineSource.RankCommonOpen.BundleCycles.affineSpaceSourceRank_commonOpen p q
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase C.coefficient (C.coefficient × C.module))
    j C.totalMap C.baseMap hj C.square.w f r C.rank hq hC u).symm⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ChartsRankFromOpen.BundleCycles
