import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowReindex

/-! # Chow Reindex -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowReindex.BundleCycles

noncomputable section

/-! Canonical Chow transports commute with open restriction and
with reindexing of equal dimensions. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem openChowRestriction_reindex {U X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian U]
    [AlgebraicGeometry.IsNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d e : ℕ) (h : d = e) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl h (ChowRestriction.BundleCycles.openChowRestriction j f d α) =
      ChowRestriction.BundleCycles.openChowRestriction j f e (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl h α) := by
  subst e
  rfl

theorem dimensionChowTransport_reindex {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    {f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (h : f = g) (d e : ℕ) (hd : d = e) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    DimensionChow.BundleCycles.dimensionChowTransport h e (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl hd α) =
      DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl hd (DimensionChow.BundleCycles.dimensionChowTransport h d α) := by
  subst g
  subst e
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowReindex.BundleCycles
