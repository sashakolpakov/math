import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.CartierChowIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Integral
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Bundle

/-! # Chow Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.ChowIntersection.BundleCycles

noncomputable section

/-! The actual infinity hyperplane has the expected signed Chow
intersection with the fundamental class of its symmetric projective compactification. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [IsIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M)]
    [IsIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M))]
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem symmetricInfinity_chowIntersection (d : ℕ)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ f) = d + 1) :
    LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (Bundle.Cycles.symmetricInfinityIdealLineBundle R M)
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ f) d
      (Point.CycleChow.BundleCycles.pointCycleToChowQ (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ f) (d + 1)
        (Finsupp.single (genericPoint (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M))) 1)) =
      -Closed.ChowPushforward.BundleCycles.closedChowPushforward (Inclusion.BundleCycles.symmetricInfinityInclusion R M)
        (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ f) d
        (Point.CycleChow.BundleCycles.pointCycleToChowQ (Inclusion.BundleCycles.symmetricInfinityInclusion R M ≫ (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ f)) d
          (Finsupp.single (genericPoint (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M)) 1)) :=
  Integral.CartierChowIntersection.BundleCycles.integralCartierIdeal_chowIntersection (Inclusion.BundleCycles.symmetricInfinityInclusion R M)
    (Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R M)
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ f) d hd

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.ChowIntersection.BundleCycles
