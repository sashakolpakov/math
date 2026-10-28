import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.AffineCompactificationChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.SourceChowComparison
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowSurjective

/-! # Projective Compactification Chow Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ProjectiveCompactificationChowEquiv.BundleCycles

noncomputable section

/-! A genuine affine-space bundle with the constructed projective
coefficient detection has Chow homotopy invariance in positive rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X D U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian D] [AlgebraicGeometry.IsNoetherian U]
    [E.IsSeparated] [X.IsSeparated] [D.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (s : D ⟶ E) [IsClosedImmersion s] [Smooth (s ≫ p)] [GeometricallyIntegral (s ≫ p)]
    (j : U ⟶ E) [IsOpenImmersion j] (hc : Set.range s = (Set.range j)ᶜ)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (HP : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (HD : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts (s ≫ p) (L.pullback s))
    (q : U ⟶ X) [Smooth q] [GeometricallyIntegral q] (hj : j ≫ p = q)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ)
    (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1))
    (hD : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (s ≫ p) r)
    (hq : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank q (r + 1))

include hc HP HD hj hp hD in
theorem affineProjectiveCompactificationChow_bijective (d : ℕ) :
    Function.Bijective (AffineBundle.ChowExtension.Cycles.affineBundleChowExtension q f (r + 1) hq d) := by
  refine ⟨?_, AffineBundle.ChowSurjective.Cycles.affineBundleChowExtension_surjective q f (r + 1) hq d⟩
  rw [AffineBundle.SourceChowComparison.Cycles.affineBundleChowExtension_eq_sourceCharts q f (r + 1) hq hq.sourceCharts d]
  exact Projective.AffineCompactificationChow.BundleCycles.affineProjectiveCompactificationChowExtension_injective p s j hc L HP HD q hj f r hp hD hq.sourceCharts d

def affineProjectiveCompactificationChowEquiv (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d ≃ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (q ≫ f) (d + (r + 1)) :=
  LinearEquiv.ofBijective (AffineBundle.ChowExtension.Cycles.affineBundleChowExtension q f (r + 1) hq d)
    (affineProjectiveCompactificationChow_bijective p s j hc L HP HD q hj f r hp hD hq d)

theorem affineProjectiveCompactificationChowEquiv_pointClass (d : ℕ) (z : X →₀ ℚ) :
    affineProjectiveCompactificationChowEquiv p s j hc L HP HD q hj f r hp hD hq d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (q ≫ f) (d + (r + 1)) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension q z) :=
  AffineBundle.ChowPointClass.Cycles.affineBundleChowExtension_pointClass q f (r + 1) hq d z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ProjectiveCompactificationChowEquiv.BundleCycles
