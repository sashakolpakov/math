import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.MomentFiltration
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.InfinityChartsChowGeneration

/-! # Moment Injective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.MomentInjective.BundleCycles

noncomputable section

/-! For actual projective bundles, the proper pushforwards of
the first intersection powers jointly detect every genuine Chow class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated] (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (H : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L) (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

include H hp in
theorem projectiveChowMoments_joint_zero (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d)
    (hz : ∀ (s n : ℕ) (h : d = s + n), n ≤ r → MomentClosed.BundleCycles.projectiveChowMoment p f L d s n h α = 0) : α = 0 := by
  apply MomentFiltration.BundleCycles.projectiveChowFiltration_joint_zero p f L r hp H d (r + 1) le_rfl α ?_ hz
  rw [Filtration.BundleCycles.projectiveChowFiltration_full]
  exact Projective.InfinityChartsChowGeneration.BundleCycles.freeInfinityCharts_chow_generated p L H r hp f d α

include H hp in
theorem projectiveChowMoments_joint_injective (d : ℕ) (α β : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d)
    (h : ∀ (s n : ℕ) (hd : d = s + n), n ≤ r →
      MomentClosed.BundleCycles.projectiveChowMoment p f L d s n hd α = MomentClosed.BundleCycles.projectiveChowMoment p f L d s n hd β) : α = β := by
  apply sub_eq_zero.mp
  apply projectiveChowMoments_joint_zero p f L H r hp d (α - β)
  intro s n hd hn
  rw [map_sub, h s n hd hn, sub_self]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.MomentInjective.BundleCycles
