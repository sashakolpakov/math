import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowPower

/-! # Chow Open Power -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOpenPower.Cycles

noncomputable section

/-! Genuine line-bundle Chow powers commute with open restriction. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {U X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian U]
    [AlgebraicGeometry.IsNoetherian X] [U.IsSeparated] [X.IsSeparated]
    (i : U ⟶ X) [IsOpenImmersion i] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem separatedLineBundleChowIntersection_open (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f (d + 1)) :
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d (SeparatedChow.Cycles.separatedLineBundleChowIntersection L f d α) =
      SeparatedChow.Cycles.separatedLineBundleChowIntersection (L.pullback i) (i ≫ f) d
        (Open.ChowRestriction.BundleCycles.openChowRestriction i f (d + 1) α) := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f (d + 1) α
  rw [SeparatedChow.Cycles.separatedLineBundleChowIntersection_cycle, Open.ChowRestriction.BundleCycles.openChowRestriction_cycle i f (d + 1),
    SeparatedChow.Cycles.separatedLineBundleChowIntersection_cycle]
  exact (OpenIntersection.Cycles.lineBundleCycleIntersection_open_restriction i L f d z).symm

theorem separatedLineBundleChowPower_open (d n : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f (d + n)) :
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d (SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d n α) =
      SeparatedChowPower.Cycles.separatedLineBundleChowPower (L.pullback i) (i ≫ f) d n
        (Open.ChowRestriction.BundleCycles.openChowRestriction i f (d + n) α) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [SeparatedChowPower.Cycles.separatedLineBundleChowPower_succ, ih, separatedLineBundleChowIntersection_open]
    rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOpenPower.Cycles
