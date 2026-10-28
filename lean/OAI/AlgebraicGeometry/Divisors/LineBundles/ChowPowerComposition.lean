import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowPower
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowReindex

/-! # Chow Power Composition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ChowPowerComposition.BundleCycles

noncomputable section

section

/-! Reindexing equal dimensions commutes with the constructed
intersection powers and closed Chow pushforwards. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem separatedLineBundleChowPower_reindex {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [X.IsSeparated] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d e n : ℕ) (h : d = e) (α : DimensionChow.BundleCycles.DimensionChowQ f (d + n)) :
    DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl h (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d n α) =
      LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L f e n
        (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl (congrArg (fun k => k + n) h) α) := by
  subst e
  rfl

theorem separatedLineBundleChowIntersection_reindex {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [X.IsSeparated] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d e : ℕ) (h : d = e) (α : DimensionChow.BundleCycles.DimensionChowQ f (d + 1)) :
    DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl h (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection L f d α) =
      LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection L f e
        (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl (congrArg (fun k => k + 1) h) α) := by
  subst e
  rfl

theorem closedChowPushforwardOver_reindex {X Y : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (j : X ⟶ Y) [IsClosedImmersion j] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType g] (hj : j ≫ g = f) (d e : ℕ) (h : d = e) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl h (Closed.ChowOver.BundleCycles.closedChowPushforwardOver j f g hj d α) =
      Closed.ChowOver.BundleCycles.closedChowPushforwardOver j f g hj e (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl h α) := by
  subst e
  rfl

end

/-! Actual repeated Chow intersections compose by adding their
exponents, with the canonical associativity transport of dimensions. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem dimensionChowReindexEquiv_trans {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) {d e k : ℕ} (h : d = e) (h' : e = k) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl h' (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl h α) =
      DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl (h.trans h') α := by
  subst e
  subst k
  rfl

theorem separatedLineBundleChowPower_add {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [X.IsSeparated] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d n m : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f ((d + n) + m)) :
    LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d n (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L f (d + n) m α) =
      LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d (n + m)
        (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl (Nat.add_assoc d n m) α) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d n
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L f (d + n) m
        (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection L f ((d + n) + m) α)) =
      LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d (n + m)
        (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection L f (d + (n + m))
          (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl (Nat.add_assoc d n (m + 1)) α))
    rw [ih]
    exact congrArg (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d (n + m))
      (separatedLineBundleChowIntersection_reindex L f ((d + n) + m) (d + (n + m))
        (Nat.add_assoc d n m) α)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ChowPowerComposition.BundleCycles
