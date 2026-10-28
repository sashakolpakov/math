import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowPower
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowFunctoriality

/-! # Chow Over Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOverProjection.Cycles

noncomputable section

/-! Actual repeated Chow intersection is compatible with proper
pushforward and explicit transport of the structure morphisms. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated] (i : X ⟶ Y) [IsProper i]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (h : i ≫ g = f)

omit [LocallyOfFiniteType f] in
theorem properChowPushforwardOver_eq_closed [IsClosedImmersion i] (d : ℕ) :
    Proper.ChowFunctoriality.BundleCycles.properChowPushforwardOver i f g h d = Closed.ChowOver.BundleCycles.closedChowPushforwardOver i f g h d := by
  change (Proper.ChowNe.BundleCycles.properChowPushforward i g d).comp (DimensionChow.BundleCycles.dimensionChowTransport h.symm d) = _
  rw [Proper.ChowFunctoriality.BundleCycles.properChowPushforward_eq_closed]
  rfl

theorem separatedLineBundleChowPower_properOver_projection (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)
    (d n : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f (d + n)) :
    Proper.ChowFunctoriality.BundleCycles.properChowPushforwardOver i f g h d (SeparatedChowPower.Cycles.separatedLineBundleChowPower (L.pullback i) f d n α) =
      SeparatedChowPower.Cycles.separatedLineBundleChowPower L g d n (Proper.ChowFunctoriality.BundleCycles.properChowPushforwardOver i f g h (d + n) α) := by
  subst f
  exact SeparatedChowPower.Cycles.separatedLineBundleChowPower_proper_projection i g L d n α

theorem separatedLineBundleChowPower_transport {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [X.IsSeparated] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f = g) (d n : ℕ)
    (α : DimensionChow.BundleCycles.DimensionChowQ f (d + n)) :
    DimensionChow.BundleCycles.dimensionChowTransport h d (SeparatedChowPower.Cycles.separatedLineBundleChowPower L f d n α) =
      SeparatedChowPower.Cycles.separatedLineBundleChowPower L g d n (DimensionChow.BundleCycles.dimensionChowTransport h (d + n) α) := by
  subst g
  rfl

theorem properChowPushforward_closedOver_comp
    {E X D : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian D]
    [E.IsSeparated] [X.IsSeparated] [D.IsSeparated]
    (p : E ⟶ X) [IsProper p] (s : D ⟶ E) [IsClosedImmersion s]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)
    (α : DimensionChow.BundleCycles.DimensionChowQ ((s ≫ p) ≫ f) d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm d α) =
      Proper.ChowNe.BundleCycles.properChowPushforward (s ≫ p) f d α := by
  have H := Proper.ChowFunctoriality.BundleCycles.properChowPushforwardOver_comp s ((s ≫ p) ≫ f) (p ≫ f)
    (Category.assoc s p f).symm p f rfl d α
  rw [properChowPushforwardOver_eq_closed s] at H
  exact H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOverProjection.Cycles
