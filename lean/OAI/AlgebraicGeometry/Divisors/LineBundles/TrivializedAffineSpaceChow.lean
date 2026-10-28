import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChowExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChowVanishing

/-! # Trivialized Affine Space Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.TrivializedAffineSpaceChow.BundleCycles

noncomputable section

/-! # LineBundleCycles: genuine Chow homotopy invariance for an actual global affine-space trivialization -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    {E : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    (p : E ⟶ X) [LocallyOfFiniteType p] (ι : Type) [Finite ι]
    (e : AffineSpace ι X ≅ E) (he : e.hom ≫ p = (AffineSpace ι X ↘ X))

include e he

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian E]
  [LocallyOfFiniteType f] [LocallyOfFiniteType p] [Finite ι] in
theorem affineSpaceTrivialization_over_complex :
    e.hom ≫ (p ≫ f) = (AffineSpace ι X ↘ X) ≫ f := by
  rw [← Category.assoc, he]

def trivializedAffineSpaceChowEquiv (d : ℕ) :
    DimensionChow.BundleCycles.DimensionChowQ f d ≃ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) (d + Nat.card ι) :=
  (FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv X f ι d).trans
    (Closed.ChowOver.BundleCycles.schemeIsoChowEquiv e ((AffineSpace ι X ↘ X) ≫ f) (p ≫ f)
      (affineSpaceTrivialization_over_complex X f p ι e he) (d + Nat.card ι))

theorem trivializedAffineSpaceChowEquiv_pointClass [GeometricallyIntegral p]
    (d : ℕ) (z : X →₀ ℚ) :
    trivializedAffineSpaceChowEquiv X f p ι e he d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d z) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + Nat.card ι) (Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension p z) := by
  rw [trivializedAffineSpaceChowEquiv, LinearEquiv.trans_apply,
    FiniteAffine.SpaceChow.BundleCycles.affineSpaceChowEquiv_pointClass, Closed.ChowPointClass.BundleCycles.schemeIsoChowEquiv_pointClass]
  apply congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ (p ≫ f) (d + Nat.card ι))
  change Finsupp.mapDomain e.hom
      (Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (AffineSpace ι X ↘ X)) z) =
    Finsupp.mapDomain (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint p) z
  rw [← Finsupp.mapDomain_comp]
  exact congrArg (fun k => Finsupp.mapDomain k z)
    (funext (Integral.FiberComposition.BundleCycles.integralFiberGenericPoint_iso e _ p he))

theorem trivializedAffineSpace_chow_eq_zero_below_rank (d : ℕ) (hd : d < Nat.card ι)
    (a : DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d) : a = 0 := by
  let c := Closed.ChowOver.BundleCycles.schemeIsoChowEquiv e ((AffineSpace ι X ↘ X) ≫ f) (p ≫ f)
    (affineSpaceTrivialization_over_complex X f p ι e he) d
  apply c.symm.injective
  rw [map_zero]
  exact LineBundles.AffineSpace.ChowVanishing.BundleCycles.affineSpace_chow_eq_zero_below_rank X f ι d hd (c.symm a)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.TrivializedAffineSpaceChow.BundleCycles
