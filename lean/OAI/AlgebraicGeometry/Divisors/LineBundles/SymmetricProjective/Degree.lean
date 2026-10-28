import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Has
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IsomorphicDivisorDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.ChowIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass

/-! # Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Degree.BundleCycles

noncomputable section

/-! The actual projective line has infinity-ideal degree minus one,
computed with genuine Chow pullback, intersection, and proper pushforward. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsNoetherianRing R]
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

def symmetricProjectiveLineChowExtension (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R) ≫ f) (d + 1) := by
  let : Smooth (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) := (Has.BundleCycles.symmetricProjectiveLine_hasSourceCharts R).forget.smooth
  exact AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) f 1
    (Has.BundleCycles.symmetricProjectiveLine_hasSourceCharts R) d

theorem symmetricProjectiveLineChowExtension_pointClass (d : ℕ) (z : Spec (.of R) →₀ ℚ) :
    symmetricProjectiveLineChowExtension R f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R) ≫ f) (d + 1)
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) z) := by
  let : Smooth (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) := (Has.BundleCycles.symmetricProjectiveLine_hasSourceCharts R).forget.smooth
  exact AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) f 1
    (Has.BundleCycles.symmetricProjectiveLine_hasSourceCharts R) d z

variable [IsDomain R]

theorem symmetricProjectiveLine_infinity_degree (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) f d
      (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R R)
        (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R) ≫ f) d
        (Point.CycleChow.BundleCycles.pointCycleToChowQ (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R) ≫ f) (d + 1)
          (Finsupp.single (genericPoint (Scheme.BundleCycles.symmetricProjectiveScheme R (R × R))) 1))) =
      -Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single (genericPoint (Spec (.of R))) 1) := by
  let : IsIso (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R R ≫ Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) := by
    have h : SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R R ≫ Scheme.BundleCycles.symmetricProjectiveToBase R (R × R) =
        Scheme.BundleCycles.symmetricProjectiveToBase R R :=
      Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd R R R) (fun r => ⟨(0, r), rfl⟩)
    rw [h]
    infer_instance
  exact Cartier.IsomorphicDivisorDegree.BundleCycles.cartierIsomorphicDivisor_chowIntersection_pushforward (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R))
    (SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R R) (SymmetricInfinity.Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R R) f d
    (by rw [Has.BundleCycles.symmetricProjectiveLine_dimension R f, hd])

theorem symmetricProjectiveLine_pullback_infinity_degree (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R)) f d
      (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R R)
        (Scheme.BundleCycles.symmetricProjectiveToBase R (R × R) ≫ f) d
        (symmetricProjectiveLineChowExtension R f d
          (Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single (genericPoint (Spec (.of R))) 1)))) =
      -Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Finsupp.single (genericPoint (Spec (.of R))) 1) := by
  rw [symmetricProjectiveLineChowExtension_pointClass]
  change Proper.ChowNe.BundleCycles.properChowPushforward _ _ _ (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection _ _ _
    (Point.CycleChow.BundleCycles.pointCycleToChowQ _ _ (Finsupp.mapDomain _ (Finsupp.single _ 1)))) = _
  rw [Finsupp.mapDomain_single, Integral.FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic]
  exact symmetricProjectiveLine_infinity_degree R f d hd

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Degree.BundleCycles
