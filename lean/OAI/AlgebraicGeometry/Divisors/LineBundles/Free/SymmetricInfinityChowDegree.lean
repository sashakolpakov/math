import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteBasisIteratedEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.IteratedProjectiveChowDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Equiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeIso

/-! # Symmetric Infinity Chow Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.SymmetricInfinityChowDegree.BundleCycles

noncomputable section

/-! The actual infinity ideal has the expected top intersection
degree on every finite free augmented projective bundle. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Fintype ι] (b : Module.Basis ι R M)
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (n : ℕ) (hn : Nat.card ι = n + 1)
    (h : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) (n + 1))

include b hn in
theorem freeSymmetricInfinityChow_top_degree (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M)
        (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ f) d (n + 1)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) f (n + 1) h d α)) =
      (-1 : ℚ) ^ (n + 1) • α := by
  let e := FiniteBasisIteratedEquiv.BundleCycles.finiteBasisIteratedEquiv b n hn
  let j := (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveIso (SymmetricInfinity.Equiv.BundleCycles.augmentedLinearEquiv e)).inv
  have hj : j ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) =
      SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n) :=
    SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (SymmetricInfinity.Equiv.BundleCycles.augmentedLinearEquiv e).toLinearMap (SymmetricInfinity.Equiv.BundleCycles.augmentedLinearEquiv e).surjective
  have H := AffineSource.ChowDegreeIso.BundleCycles.affineSourceChowDegree_iso (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))
    (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n)) j hj f
    (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M) (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n))
    (SymmetricInfinity.Equiv.BundleCycles.symmetricInfinity_linearEquiv_idealIso e) (n + 1) h (FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_sourceCharts R (n + 1)) d α
  exact H.trans (IteratedProjectiveChowDegree.BundleCycles.iteratedProjectiveChow_top_degree R f n d α)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.SymmetricInfinityChowDegree.BundleCycles
