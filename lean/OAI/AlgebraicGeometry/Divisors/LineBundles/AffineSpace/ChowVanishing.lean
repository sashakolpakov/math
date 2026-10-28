import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteAffine.SpaceChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.ChowZero

/-! # Chow Vanishing -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChowVanishing.BundleCycles

noncomputable section

/-! # LineBundleCycles: Chow groups below the relative affine-space rank vanish -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem affineSpaceSucc_zeroDimension_chow_eq_zero (n : ℕ)
    (a : DimensionChow.BundleCycles.DimensionChowQ ((AffineSpace (Fin (n + 1)) X ↘ X) ≫ f) 0) : a = 0 := by
  let e := Closed.ChowOver.BundleCycles.schemeIsoChowEquiv
    (CoordinateEquiv.BundleCycles.affineSpaceSuccEquiv X n)
    ((AffineSpace (Fin (n + 1)) X ↘ X) ≫ f)
    (AffineLine.Charts.BundleCycles.affineLineProjection (AffineSpace (Fin n) X) ≫ ((AffineSpace (Fin n) X ↘ X) ≫ f))
    (SuccChow.BundleCycles.affineSpaceSuccEquiv_over_complex X f n) 0
  apply e.injective
  rw [map_zero]
  exact AffineLine.ChowZero.BundleCycles.affineLineZeroDimension_chow_eq_zero (AffineSpace (Fin n) X)
    ((AffineSpace (Fin n) X ↘ X) ≫ f) (e a)

theorem affineSpaceFin_chow_eq_zero_below_rank (n d : ℕ) (hd : d < n)
    (a : DimensionChow.BundleCycles.DimensionChowQ ((AffineSpace (Fin n) X ↘ X) ≫ f) d) : a = 0 := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero => exact affineSpaceSucc_zeroDimension_chow_eq_zero X f n a
    | succ d =>
      let e := SuccChow.BundleCycles.affineSpaceSuccChowEquiv X f n d
      apply e.symm.injective
      rw [map_zero]
      exact ih d (Nat.lt_of_succ_lt_succ hd) (e.symm a)

theorem affineSpace_chow_eq_zero_below_rank (ι : Type) [Finite ι] (d : ℕ) (hd : d < Nat.card ι)
    (a : DimensionChow.BundleCycles.DimensionChowQ ((AffineSpace ι X ↘ X) ≫ f) d) : a = 0 := by
  let e := Closed.ChowOver.BundleCycles.schemeIsoChowEquiv (CoordinateEquiv.BundleCycles.affineSpaceReindexEquiv X (Finite.equivFin ι))
    ((AffineSpace ι X ↘ X) ≫ f) ((AffineSpace (Fin (Nat.card ι)) X ↘ X) ≫ f)
    (FiniteAffine.SpaceChow.BundleCycles.affineSpaceReindexEquiv_over_complex X f (Finite.equivFin ι)) d
  apply e.injective
  rw [map_zero]
  exact affineSpaceFin_chow_eq_zero_below_rank X f (Nat.card ι) d hd (e a)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.ChowVanishing.BundleCycles
