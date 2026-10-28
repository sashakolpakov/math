import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperProjectionOn
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowIntersection

/-! # Proper Chow Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperChowIntersection.Cycles

noncomputable section

/-! Proper pushforward commutes with genuine line-bundle Chow intersection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated] (f : X ⟶ Y) [IsProper f]
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)

theorem lineBundleCycleIntersection_proper_projection (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (f ≫ gY) (d + 1) →₀ ℚ) :
    Proper.ChowNe.BundleCycles.properChowPushforward f gY d
      (DimensionChow.BundleCycles.dimensionCycleToChowQ (f ≫ gY) d (Intersection.Cycles.lineBundleCycleIntersection (L.pullback f) (f ≫ gY) d z)) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ gY d
        (Intersection.Cycles.lineBundleCycleIntersection L gY d (DimensionPointPushforward.BundleCycles.dimensionPointPushforward f gY (d + 1) z)) := by
  have hz : ∀ x, Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (f ≫ gY) (d + 1) z x ≠ 0 →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ gY) = d + 1 := by
    intro x hx
    by_contra hn
    apply hx
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    exact hn (ha ▸ a.property)
  have h := ProperProjectionOn.Cycles.lineBundlePointIntersection_proper_projection f gY L d
    (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (f ≫ gY) (d + 1) z) hz
  rw [Intersection.Cycles.lineBundlePointIntersection_graded, Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion,
    ← DimensionPointPushforward.BundleCycles.dimensionPointPushforward_forget, Intersection.Cycles.lineBundlePointIntersection_graded,
    Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion] at h
  exact h

theorem lineBundleChowIntersection_proper_projection
    {BX BY : Scheme.{0}} {bX : BX ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {bY : BY ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    (PX : Foundations.Scheme.SmoothProjective.ProjectivePresentation BX bX) (PY : Foundations.Scheme.SmoothProjective.ProjectivePresentation BY bY)
    (qX : X ⟶ BX) [IsAffineHom qX] (qY : Y ⟶ BY) [IsAffineHom qY]
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (f ≫ gY) (d + 1)) :
    Proper.ChowNe.BundleCycles.properChowPushforward f gY d
      (ChowIntersection.Cycles.lineBundleChowIntersection PX qX (L.pullback f) (f ≫ gY) d α) =
    ChowIntersection.Cycles.lineBundleChowIntersection PY qY L gY d (Proper.ChowNe.BundleCycles.properChowPushforward f gY (d + 1) α) := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (f ≫ gY) (d + 1) α
  rw [ChowIntersection.Cycles.lineBundleChowIntersection_cycle, Proper.ChowNe.BundleCycles.properChowPushforward_cycle f gY (d + 1), ChowIntersection.Cycles.lineBundleChowIntersection_cycle]
  exact lineBundleCycleIntersection_proper_projection f gY L d z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperChowIntersection.Cycles
