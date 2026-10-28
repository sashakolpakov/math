import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveDegreeBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.DegreeIsoBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteBasisIteratedEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Equiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.ZeroModuleProjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsomorphismDegree

/-! # Projective Degree Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveDegreeBaseChange.BundleCycles

noncomputable section

/-! A finite free augmented projective bundle has its actual
top intersection degree after any scheme base change, in every rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Fintype ι] (basis : Module.Basis ι R M)
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (b : Y ⟶ Spec (.of R)) (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hr : Nat.card ι = r)
    (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) r)

include basis hr in
theorem freeProjectiveChow_baseChange_degree (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower ((SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M).pullback
        (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b))
        (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b ≫ f) d r
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b)
          f r (hp.baseChange b) d α)) = (-1 : ℚ) ^ r • α := by
  cases r with
  | zero =>
    let : IsIso (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) :=
      ZeroModuleProjective.BundleCycles.symmetricAugmentedProjective_isIso_of_basis_card_zero basis hr
    rw [pow_zero, one_smul]
    exact AffineSource.ChowIsomorphismDegree.BundleCycles.affineSpaceSourceChowExtension_isomorphism_degree
      (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) b) f (hp.baseChange b) d α
  | succ n =>
    let e := FiniteBasisIteratedEquiv.BundleCycles.finiteBasisIteratedEquiv basis n hr
    let j := (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (SymmetricInfinity.Equiv.BundleCycles.augmentedLinearEquiv e)).inv
    have hj : j ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) =
        SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n) :=
      SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (SymmetricInfinity.Equiv.BundleCycles.augmentedLinearEquiv e).toLinearMap (SymmetricInfinity.Equiv.BundleCycles.augmentedLinearEquiv e).surjective
    have H := AffineSource.DegreeIsoBaseChange.BundleCycles.affineSourceChowDegree_iso_baseChange (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n)) j hj b f
      (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M) (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n))
      (SymmetricInfinity.Equiv.BundleCycles.symmetricInfinity_linearEquiv_idealIso e) (n + 1) hp (FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_sourceCharts R (n + 1)) d α
    exact H.trans (ProjectiveDegreeBaseChange.BundleCycles.iteratedProjectiveChow_baseChange_degree R b f n d α)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveDegreeBaseChange.BundleCycles
