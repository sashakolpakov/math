import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.CycleCoordinates
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceProperties
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.IsoChow

/-! # Succ Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SuccChow.BundleCycles

noncomputable section

/-! # LineBundleCycles: one-step genuine Chow homotopy invariance for finite affine spaces -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

omit [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType f] in
theorem affineSpaceSuccEquiv_over_complex (n : ℕ) :
    (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).hom ≫
      (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X) ≫ ((AffineSpace (Fin n) X ↘ X) ≫ f)) =
      (AffineSpace (Fin (n + 1)) X ↘ X) ≫ f := by
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ f) (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv_over X n))

def affineSpaceSuccChowEquiv (n d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ ((AffineSpace (Fin n) X ↘ X) ≫ f) d ≃ₗ[ℚ]
      DimensionChow.BundleCycles.DimensionChowQ ((AffineSpace (Fin (n + 1)) X ↘ X) ≫ f) (d + 1) :=
  AffineLine.IsoChow.BundleCycles.affineLineIsoChowEquiv (AffineSpace (Fin n) X) ((AffineSpace (Fin n) X ↘ X) ≫ f)
    (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).symm ((AffineSpace (Fin (n + 1)) X ↘ X) ≫ f)
    (Closed.ChowOver.BundleCycles.schemeIso_inverse_over _ _ _ (affineSpaceSuccEquiv_over_complex X f n)) d

theorem affineSpaceSuccChowEquiv_pointClass (n d : ℕ) (z : AffineSpace (Fin n) X →₀ ℚ) :
    affineSpaceSuccChowEquiv X f n d (Point.CycleChow.BundleCycles.pointCycleToChowQ ((AffineSpace (Fin n) X ↘ X) ≫ f) d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ ((AffineSpace (Fin (n + 1)) X ↘ X) ≫ f) (d + 1)
        (Finsupp.mapDomain (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).symm.hom
          (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X)) z)) := by
  rw [affineSpaceSuccChowEquiv]
  exact AffineLine.IsoChow.BundleCycles.affineLineIsoChowEquiv_pointClass (AffineSpace (Fin n) X) ((AffineSpace (Fin n) X ↘ X) ≫ f)
    (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).symm ((AffineSpace (Fin (n + 1)) X ↘ X) ≫ f)
    (Closed.ChowOver.BundleCycles.schemeIso_inverse_over _ _ _ (affineSpaceSuccEquiv_over_complex X f n)) d z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SuccChow.BundleCycles
