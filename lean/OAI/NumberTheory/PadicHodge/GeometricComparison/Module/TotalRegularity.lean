import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalCoordinates
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Regular.SMul

/-! # Total Regularity -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalRegularity.ModuleTotalRegularity

noncomputable section

/-! Regular coefficients stay regular on categorical module products and first-quadrant totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {R : Type u} [CommRing R]

theorem product {ι : Type v} (M : ι → ModuleCat.{v} R) (r : R)
    (h : ∀ i, IsSMulRegular (M i) r) : IsSMulRegular (∏ᶜ M : ModuleCat.{v} R) r := by
  intro x y hxy
  apply (ModuleCat.piIsoPi M).toLinearEquiv.injective
  funext i
  apply h i
  exact (map_smul (Pi.π M i).hom r x).symm.trans
    ((congrArg (Pi.π M i) hxy).trans (map_smul (Pi.π M i).hom r y))

theorem total (K : HomologicalComplex₂ (ModuleCat.{v} R) (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)] (r : R) (h : ∀ q p, IsSMulRegular ((K.X q).X p) r) (n : ℕ) :
    IsSMulRegular ((K.total (.up ℕ)).X n) r := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  apply IntegralComparison.Module.TotalCoordinates.eq_zero_of_coordinates K n x
  intro i
  apply (h i (n - i)).right_eq_zero_of_smul
  exact (map_smul ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) i (n - i) n).hom r x).symm.trans
    ((congrArg ((AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) i (n - i) n) hx).trans (map_zero _))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.TotalRegularity.ModuleTotalRegularity
