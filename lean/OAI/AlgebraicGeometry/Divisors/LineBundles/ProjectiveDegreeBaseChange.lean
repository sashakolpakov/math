import OAI.AlgebraicGeometry.Divisors.LineBundles.IteratedProjectiveChowDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.CurveDegreeBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.DegreeBaseChange

/-! # Projective Degree Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveDegreeBaseChange.BundleCycles

noncomputable section

/-! Repeated hyperplane intersection in a finite free projective
bundle has the expected degree after an arbitrary base change. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (R : Type) [CommRing R] {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (b : Y ⟶ Spec (.of R)) (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem iteratedProjectiveChow_baseChange_degree (n d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n)) b) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower ((SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n)).pullback
        (pullback.fst (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n)) b))
        (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n)) b ≫ f) d (n + 1)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension
          (pullback.snd (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n)) b)
          f (n + 1) ((FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_sourceCharts R (n + 1)).baseChange b) d α)) =
      (-1 : ℚ) ^ (n + 1) • α := by
  induction n with
  | zero =>
    rw [pow_one, neg_one_smul, IteratedProjectiveChowDegree.BundleCycles.separatedLineBundleChowPower_one]
    let p := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R 0)
    let s := SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R 0)
    let : IsIso (s ≫ p) := by
      have he : s ≫ p = SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R 0) :=
        SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd R R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R 0)) _
      rw [he]
      exact inferInstanceAs (IsIso (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R R))
    exact Cartier.CurveDegreeBaseChange.BundleCycles.cartierCurveChow_baseChange_degree p s
      (SymmetricInfinity.Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R 0)) b f
      (FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_sourceCharts R 1) d α
  | succ n ih =>
    let : Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n))) :=
      FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_smooth R ((n + 1) + 1)
    let : GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n))) :=
      FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_geometricallyIntegral R ((n + 1) + 1)
    have H := SymmetricInfinity.DegreeBaseChange.BundleCycles.symmetricInfinityChow_degree_baseChange_step R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n) b f (n + 1)
      (FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_sourceCharts R ((n + 1) + 1)) (FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_sourceCharts R (n + 1)) d α
    have hsign : -((-1 : ℚ) ^ (n + 1) • α) = (-1 : ℚ) ^ ((n + 1) + 1) • α := by
      rw [pow_succ' (-1 : ℚ) (n + 1), mul_smul, neg_one_smul]
    exact H.trans ((congrArg Neg.neg ih).trans hsign)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveDegreeBaseChange.BundleCycles
