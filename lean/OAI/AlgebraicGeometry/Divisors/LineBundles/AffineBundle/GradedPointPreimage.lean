import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowBelowRank
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowSurjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.PointClassOffGrade

/-! # Graded Point Preimage -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.GradedPointPreimage.Cycles

noncomputable section

/-! A cycle in any one dimension grade has an actual finite point-cycle
preimage under an affine-space bundle, simultaneously in every Chow grade. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r)

include r h

theorem affineBundle_shiftedCycle_pointPreimage (d : ℕ)
    (β : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (p ≫ f) (d + r) →₀ ℚ) :
    ∃ z : X →₀ ℚ, ∀ e : ℕ,
      Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) e (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) =
        Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) e (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) (d + r) β) := by
  obtain ⟨α, hα⟩ := ChowSurjective.Cycles.affineBundleChowExtension_surjective p f r h d (DimensionChow.BundleCycles.dimensionCycleToChowQ (p ≫ f) (d + r) β)
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  refine ⟨Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z, ?_⟩
  intro e
  by_cases he : e = d + r
  · subst e
    rw [← ChowPointClass.Cycles.affineBundleChowExtension_pointClass p f r h d,
      Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion, Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion]
    exact hα
  · rw [← CycleGrading.Cycles.affineBundleGradedCycleExtension_forget p f r h d,
      PointClassOffGrade.BundleCycles.pointCycleToChowQ_inclusion_off (p ≫ f) (d + r) e (Ne.symm he),
      PointClassOffGrade.BundleCycles.pointCycleToChowQ_inclusion_off (p ≫ f) (d + r) e (Ne.symm he)]

theorem affineBundle_gradedCycle_pointPreimage (e : ℕ)
    (β : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (p ≫ f) e →₀ ℚ) :
    ∃ z : X →₀ ℚ, ∀ d : ℕ,
      Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) =
        Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) d (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (p ≫ f) e β) := by
  by_cases he : e < r
  · refine ⟨0, ?_⟩
    intro d
    rw [map_zero, map_zero]
    by_cases hd : d = e
    · subst d
      exact (ChowBelowRank.Cycles.affineBundle_chow_eq_zero_below_rank p f r h e he _).symm
    · exact (PointClassOffGrade.BundleCycles.pointCycleToChowQ_inclusion_off (p ≫ f) e d (Ne.symm hd) β).symm
  · obtain ⟨d, hd⟩ := Nat.le.dest (Nat.le_of_not_gt he)
    have heq : e = d + r := by omega
    clear hd
    subst e
    exact affineBundle_shiftedCycle_pointPreimage p f r h d β

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.GradedPointPreimage.Cycles
