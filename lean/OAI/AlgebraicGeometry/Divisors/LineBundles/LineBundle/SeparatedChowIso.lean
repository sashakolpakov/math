import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowPower
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IntersectionComparison

/-! # Separated Chow Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowIso.Cycles

noncomputable section

/-! Genuine Chow intersection and its powers depend only on
the isomorphism class of the actual algebraic line bundle. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
    {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} (e : L.sheaf ≅ M.sheaf)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include e

theorem separatedLineBundleChowIntersection_iso (d : ℕ) :
    SeparatedChow.Cycles.separatedLineBundleChowIntersection L f d = SeparatedChow.Cycles.separatedLineBundleChowIntersection M f d := by
  ext α
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f (d + 1) α
  exact IntersectionComparison.Cycles.lineBundleCycleIntersection_class_iso f d e z

theorem separatedLineBundleChowPower_iso (d n : ℕ) :
    SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d n = SeparatedChowPower.Cycles.separatedLineBundleChowPower M f d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d n).comp (SeparatedChow.Cycles.separatedLineBundleChowIntersection L f (d + n)) =
      (SeparatedChowPower.Cycles.separatedLineBundleChowPower M f d n).comp (SeparatedChow.Cycles.separatedLineBundleChowIntersection M f (d + n))
    rw [ih, separatedLineBundleChowIntersection_iso e f]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowIso.Cycles
