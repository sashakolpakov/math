import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierDegreeBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.IdealRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Integral

/-! # Degree Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.DegreeBaseChange.BundleCycles

noncomputable section

/-! The actual infinity hyperplane lowers projective intersection
degree by one after every change of the coefficient scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M)))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M)))]
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (b : Y ⟶ Spec (.of R)) (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ)
    (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) (r + 1))
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) r)

theorem symmetricInfinityChow_degree_baseChange_step (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) b) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower ((Bundle.Cycles.symmetricInfinityIdealLineBundle R (R × M)).pullback
        (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) b))
        (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) b ≫ f) d (r + 1)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M))) b)
          f (r + 1) (hp.baseChange b) d α)) =
      -Proper.ChowNe.BundleCycles.properChowPushforward (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b) f d
        (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower ((Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback
          (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b))
          (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b ≫ f) d r
          (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b)
            f r (hq.baseChange b) d α)) := by
  exact Relative.CartierDegreeBaseChange.BundleCycles.relativeCartierDegree_baseChange (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × M)))
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) (Inclusion.BundleCycles.symmetricInfinityInclusion R (R × M))
    (SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd R R (R × M)) _)
    (Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R (R × M)) b f r hp hq
    (Bundle.Cycles.symmetricInfinityIdealLineBundle R M) (IdealRestriction.BundleCycles.symmetricInfinityIdealRestrictionIso R M) d α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.DegreeBaseChange.BundleCycles
