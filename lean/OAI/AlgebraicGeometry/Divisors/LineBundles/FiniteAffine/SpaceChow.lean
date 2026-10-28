import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.FinChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleGrading

/-! # Space Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceChow.BundleCycles

noncomputable section

/-! # LineBundleCycles: genuine Chow homotopy invariance for every finite set of affine coordinates -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

omit [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType f] in
theorem affineSpaceReindexEquiv_over_complex {ι κ : Type} (e : ι ≃ κ) :
    (LineBundles.AffineSpace.CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X e).hom ≫ ((AffineSpace κ X ↘ X) ≫ f) =
      (AffineSpace ι X ↘ X) ≫ f := by
  rw [← Category.assoc, LineBundles.AffineSpace.CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv_over]

def affineSpaceChowEquiv (ι : Type) [Finite ι] (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d ≃ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι) :=
  (LineBundles.AffineSpace.FinChow.BundleCycles.affineSpaceFinChowEquiv X f (Nat.card ι) d).trans
    (Closed.ChowOver.BundleCycles.schemeIsoChowEquiv (LineBundles.AffineSpace.CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X (Finite.equivFin ι).symm)
      ((AffineSpace (Fin (Nat.card ι)) X ↘ X) ≫ f) ((AffineSpace ι X ↘ X) ≫ f)
      (affineSpaceReindexEquiv_over_complex X f (Finite.equivFin ι).symm) (d + Nat.card ι))

theorem affineSpaceChowEquiv_pointClass (ι : Type) [Finite ι] (d : ℕ) (z : X →₀ ℚ) :
    affineSpaceChowEquiv X f ι d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι)
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineSpace ι X ↘ X) z) := by
  rw [affineSpaceChowEquiv, LinearEquiv.trans_apply, LineBundles.AffineSpace.FinChow.BundleCycles.affineSpaceFinChowEquiv_pointClass,
    Closed.ChowPointClass.BundleCycles.schemeIsoChowEquiv_pointClass]
  apply congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ ((AffineSpace ι X ↘ X) ≫ f) (d + Nat.card ι))
  change Finsupp.mapDomain (LineBundles.AffineSpace.CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X (Finite.equivFin ι).symm).hom
      (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin (Nat.card ι)) X ↘ X)) z) =
    Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace ι X ↘ X)) z
  rw [← Finsupp.mapDomain_comp]
  exact congrArg (fun k => Finsupp.mapDomain k z)
    (funext (LineBundles.AffineSpace.CycleCoordinates.BundleCycles.affineSpaceReindexEquiv_fiberGeneric X (Finite.equivFin ι).symm))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceChow.BundleCycles
