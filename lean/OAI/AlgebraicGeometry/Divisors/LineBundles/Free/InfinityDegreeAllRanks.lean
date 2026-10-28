import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.SymmetricInfinityChowDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.ZeroModuleProjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsomorphismDegree

/-! # Infinity Degree All Ranks -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityDegreeAllRanks.BundleCycles

noncomputable section

/-! The top degree of the actual infinity ideal is valid in every
finite free rank, including the zero module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {R M ι : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Fintype ι] (b : Module.Basis ι R M)
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hr : Nat.card ι = r)
    (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) r)

include b hr in
theorem freeSymmetricInfinityChow_degree (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M)
        (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) ≫ f) d r
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) f r hp d α)) =
      (-1 : ℚ) ^ r • α := by
  cases r with
  | zero =>
    let : IsIso (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) :=
      ZeroModuleProjective.BundleCycles.symmetricAugmentedProjective_isIso_of_basis_card_zero b hr
    rw [pow_zero, one_smul]
    exact AffineSource.ChowIsomorphismDegree.BundleCycles.affineSpaceSourceChowExtension_isomorphism_degree (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) f hp d α
  | succ n => exact SymmetricInfinityChowDegree.BundleCycles.freeSymmetricInfinityChow_top_degree b f n hr hp d α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityDegreeAllRanks.BundleCycles
