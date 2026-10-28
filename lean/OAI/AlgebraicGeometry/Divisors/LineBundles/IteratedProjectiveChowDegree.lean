import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteBasisIteratedEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberChowPower
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeCongr
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.IdealRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ChowDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.ChowDegreeStep

/-! # Iterated Projective Chow Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.IteratedProjectiveChowDegree.BundleCycles

noncomputable section

/-! Iterated actual hyperplane intersection has fiber degree
the expected sign in every finite projective dimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem separatedLineBundleChowPower_one {E : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [E.IsSeparated] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (f : E ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f (d + 1)) :
    LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d 1 α = LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection L f d α := rfl

variable (R : Type) [CommRing R] [IsNoetherianRing R]
    (f : Spec (.of R) ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem iteratedProjectiveChow_top_degree (n d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n)) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n))
        (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n) ≫ f) d (n + 1)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n))
          f (n + 1) (FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_sourceCharts R (n + 1)) d α)) =
      (-1 : ℚ) ^ (n + 1) • α := by
  induction n with
  | zero =>
    rw [pow_one, neg_one_smul, separatedLineBundleChowPower_one]
    let p := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R 0)
    let s := SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R 0)
    let : IsIso (s ≫ p) := by
      have he : s ≫ p = SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R 0) :=
        SymmetricProjective.Base.BundleCycles.symmetricProjectiveMap_over (LinearMap.snd R R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R 0)) _
      rw [he]
      exact inferInstanceAs (IsIso (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R R))
    exact Cartier.CurveChowDegree.BundleCycles.cartierCurveChow_pullback_degree p (FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_sourceCharts R 1) s
      (SymmetricInfinity.Bundle.Cycles.symmetricInfinity_regularPrincipalImageIdeals R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R 0)) f d α
  | succ n ih =>
    let : Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n))) :=
      FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_smooth R ((n + 1) + 1)
    let : GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × (R × FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n))) :=
      FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_geometricallyIntegral R ((n + 1) + 1)
    have H := SymmetricInfinity.ChowDegreeStep.BundleCycles.symmetricInfinityChow_degree_step R (FiniteBasisIteratedEquiv.BundleCycles.iteratedAugmentedModule R n) f (n + 1)
      (FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_sourceCharts R ((n + 1) + 1)) (FiniteBasisIteratedEquiv.BundleCycles.iteratedProjective_sourceCharts R (n + 1)) d α
    have hsign : -((-1 : ℚ) ^ (n + 1) • α) = (-1 : ℚ) ^ ((n + 1) + 1) • α := by
      rw [pow_succ' (-1 : ℚ) (n + 1), mul_smul, neg_one_smul]
    exact H.trans ((congrArg Neg.neg ih).trans hsign)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.IteratedProjectiveChowDegree.BundleCycles
