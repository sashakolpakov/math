import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SuccChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowReindex

/-! # Fin Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.FinChow.BundleCycles

noncomputable section

/-! # LineBundleCycles: iterated genuine Chow homotopy invariance for finite-dimensional affine space -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

omit [AlgebraicGeometry.IsNoetherian X] [LocallyOfFiniteType f] in
theorem affineSpaceEmptyEquiv_inverse_over_complex :
    (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X (Fin 0)).inv ≫ ((AffineSpace (Fin 0) X ↘ X) ≫ f) = f := by
  rw [← Category.assoc]
  change ((CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X (Fin 0)).inv ≫ (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X (Fin 0)).hom) ≫ f = f
  rw [Iso.inv_hom_id, Category.id_comp]

def affineSpaceFinChowEquiv : (n d : ℕ) →
    DimensionChow.BundleCycles.DimensionChowQ f d ≃ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ ((AffineSpace (Fin n) X ↘ X) ≫ f) (d + n)
  | 0, d => Closed.ChowOver.BundleCycles.schemeIsoChowEquiv (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X (Fin 0)).symm _ _
      (affineSpaceEmptyEquiv_inverse_over_complex X f) d
  | n + 1, d => ((affineSpaceFinChowEquiv n d).trans
      (SuccChow.BundleCycles.affineSpaceSuccChowEquiv X f n (d + n))).trans
        (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl (Nat.add_assoc d n 1))

theorem affineSpaceFinChowEquiv_pointClass (n d : ℕ) (z : X →₀ ℚ) :
    BundleCycles.affineSpaceFinChowEquiv X f n d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ ((AffineSpace (Fin n) X ↘ X) ≫ f) (d + n)
        (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (AffineSpace (Fin n) X ↘ X) z) := by
  induction n with
  | zero =>
    change Closed.ChowOver.BundleCycles.schemeIsoChowEquiv _ _ _ _ _ (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) = _
    rw [Closed.ChowPointClass.BundleCycles.schemeIsoChowEquiv_pointClass]
    apply congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ ((AffineSpace (Fin 0) X ↘ X) ≫ f) d)
    change Finsupp.mapDomain (CoordinateEquiv.BundleCycles.affineSpaceEmptyEquiv X (Fin 0)).inv z =
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin 0) X ↘ X)) z
    exact congrArg (fun k => Finsupp.mapDomain k z)
      (funext (CycleCoordinates.BundleCycles.affineSpaceEmptyEquiv_fiberGeneric X (Fin 0)))
  | succ n ih =>
    rw [BundleCycles.affineSpaceFinChowEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      ih, SuccChow.BundleCycles.affineSpaceSuccChowEquiv_pointClass, DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv_pointClass]
    apply congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ ((AffineSpace (Fin (n + 1)) X ↘ X) ≫ f) (d + (n + 1)))
    change Finsupp.mapDomain (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n).inv
        (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X)))
          (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin n) X ↘ X)) z)) =
      Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace (Fin (n + 1)) X ↘ X)) z
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    exact congrArg (fun k => Finsupp.mapDomain k z)
      (funext (CycleCoordinates.BundleCycles.affineSpaceSuccEquiv_inverse_fiberGeneric X n))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.FinChow.BundleCycles
