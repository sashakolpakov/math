import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass
import Mathlib.Tactic.IrreducibleDef

/-! # Iso Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.IsoChow.BundleCycles

noncomputable section

/-! # LineBundleCycles: affine-line Chow homotopy invariance transported through an actual scheme isomorphism -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    {Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y]
    (e : Charts.BundleCycles.affineLine X ≅ Y) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType g]
    (h : e.hom ≫ g = Charts.BundleCycles.affineLineProjection X ≫ f)

irreducible_def affineLineIsoChowEquiv (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d ≃ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ g (d + 1) :=
  (ChowEquiv.BundleCycles.affineLineChowEquiv X f d).trans
    (Closed.ChowOver.BundleCycles.schemeIsoChowEquiv e (Charts.BundleCycles.affineLineProjection X ≫ f) g h (d + 1))

theorem affineLineIsoChowEquiv_pointClass (d : ℕ) (z : X →₀ ℚ) :
    affineLineIsoChowEquiv X f e g h d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ g (d + 1)
        (Finsupp.mapDomain e.hom (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z)) := by
  rw [affineLineIsoChowEquiv_def, LinearEquiv.trans_apply,
    ChowEquiv.BundleCycles.affineLineChowEquiv_pointClass, Closed.ChowPointClass.BundleCycles.schemeIsoChowEquiv_pointClass]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.IsoChow.BundleCycles
