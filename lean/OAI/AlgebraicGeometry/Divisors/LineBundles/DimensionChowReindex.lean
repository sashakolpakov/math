import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Dimension Chow Reindex -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowReindex.BundleCycles

noncomputable section

/-! # LineBundleCycles: canonical equivalences for equal structure maps and equal dimension indices -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    {f g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {d e : ℕ}

def dimensionChowReindexEquiv (h : f = g) (hd : d = e) :
    DimensionChow.BundleCycles.DimensionChowQ f d ≃ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ g e := by
  subst g
  subst e
  exact LinearEquiv.refl ℚ _

theorem dimensionChowReindexEquiv_pointClass (h : f = g) (hd : d = e) (z : X →₀ ℚ) :
    dimensionChowReindexEquiv h hd (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) = Point.CycleChow.BundleCycles.pointCycleToChowQ g e z := by
  subst g
  subst e
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowReindex.BundleCycles
