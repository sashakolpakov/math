import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberChowPower
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeCongr
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.IdealRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Integral

/-! # Chow Degree Step -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.ChowDegreeStep.BundleCycles

noncomputable section

/-! The actual infinity hyperplane reduces the top Chern-degree
calculation by one projective dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M)))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M)))]
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ)
    (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) (r + 1))
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) r)

theorem symmetricInfinityChow_degree_step (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (Bundle.Cycles.symmetricInfinityIdealLineBundle R (R × M))
        (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M)) ≫ f) d (r + 1)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) f (r + 1) hp d α)) =
      -Proper.ChowNe.BundleCycles.properChowPushforward (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) f d
        (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (Bundle.Cycles.symmetricInfinityIdealLineBundle R M)
          (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ f) d r
          (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) f r hq d α)) := by
  let p := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))
  let s := Inclusion.BundleCycles.symmetricInfinityInclusion R (R × M)
  let q := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)
  have hs : s ≫ p = q := SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd R R (R × M)) _
  let : Smooth (s ≫ p) := by rw [hs]; infer_instance
  let : GeometricallyIntegral (s ≫ p) := by rw [hs]; infer_instance
  have hq' : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (s ≫ p) r := hs.symm ▸ hq
  have H := Relative.CartierFiberChowPower.BundleCycles.relativeCartierIdeal_topDegree_reduction p s
    (Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R (R × M)) f r hp hq'
    (Bundle.Cycles.symmetricInfinityIdealLineBundle R M) (IdealRestriction.BundleCycles.symmetricInfinityIdealRestrictionIso R M) d α
  have Hq := AffineSource.ChowDegreeCongr.BundleCycles.affineSourceChowDegree_congr (s ≫ p) q hs f (Bundle.Cycles.symmetricInfinityIdealLineBundle R M)
    r hq' hq d α
  exact H.trans (congrArg Neg.neg Hq)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.ChowDegreeStep.BundleCycles
