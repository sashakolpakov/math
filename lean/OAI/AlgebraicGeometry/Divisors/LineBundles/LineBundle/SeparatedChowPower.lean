import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperChowIntersection

/-! # Separated Chow Power -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowPower.Cycles

noncomputable section

/-! Repeated genuine line-bundle intersections and their proper projection formula. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem separatedLineBundleChowIntersection_proper_projection
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (i : X ⟶ Y) [IsProper i] (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY]
    (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y) (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (i ≫ gY) (d + 1)) :
    Proper.ChowNe.BundleCycles.properChowPushforward i gY d
      (SeparatedChow.Cycles.separatedLineBundleChowIntersection (M.pullback i) (i ≫ gY) d α) =
      SeparatedChow.Cycles.separatedLineBundleChowIntersection M gY d (Proper.ChowNe.BundleCycles.properChowPushforward i gY (d + 1) α) := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (i ≫ gY) (d + 1) α
  rw [SeparatedChow.Cycles.separatedLineBundleChowIntersection_cycle, Proper.ChowNe.BundleCycles.properChowPushforward_cycle i gY (d + 1),
    SeparatedChow.Cycles.separatedLineBundleChowIntersection_cycle]
  exact ProperChowIntersection.Cycles.lineBundleCycleIntersection_proper_projection i gY M d z

def separatedLineBundleChowPower (d : ℕ) : (n : ℕ) → (DimensionChow.BundleCycles.DimensionChowQ f (d + n) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d)
  | 0 => LinearMap.id
  | n + 1 => (separatedLineBundleChowPower d n).comp (SeparatedChow.Cycles.separatedLineBundleChowIntersection L f (d + n))

theorem separatedLineBundleChowPower_zero (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Cycles.separatedLineBundleChowPower L f d 0 α = α := rfl

theorem separatedLineBundleChowPower_succ (d n : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f (d + (n + 1))) :
    Cycles.separatedLineBundleChowPower L f d (n + 1) α =
      Cycles.separatedLineBundleChowPower L f d n (SeparatedChow.Cycles.separatedLineBundleChowIntersection L f (d + n) α) := rfl

theorem separatedLineBundleChowPower_proper_projection
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (i : X ⟶ Y) [IsProper i] (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY]
    (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y) (d n : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (i ≫ gY) (d + n)) :
    Proper.ChowNe.BundleCycles.properChowPushforward i gY d (Cycles.separatedLineBundleChowPower (M.pullback i) (i ≫ gY) d n α) =
      Cycles.separatedLineBundleChowPower M gY d n (Proper.ChowNe.BundleCycles.properChowPushforward i gY (d + n) α) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [separatedLineBundleChowPower_succ, separatedLineBundleChowPower_succ, ih,
      separatedLineBundleChowIntersection_proper_projection i gY M (d + n)]
    rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowPower.Cycles
