import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartFunctionField

/-! # Function Field Restrictions -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.FunctionFieldRestrictions

noncomputable section

/-! Canonical function-field maps commute with restriction from a
homogeneous chart to a smaller product chart. -/

open _root_.MvPolynomial _root_.HomogeneousLocalization

universe u
variable (K : Type u) [Field K] {n : ℕ}
variable (f g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0) (hg : g ≠ 0)
variable {d : ℕ} (hgd : g ∈ Hilbert.Polynomial.GradedHilbert.grading K n d)

theorem homogeneousChartFunctionFieldMap_awayMap :
    (ChartFunctionField.homogeneousChartFunctionFieldMap K (f * g) (mul_ne_zero hf hg)).comp
      (HomogeneousLocalization.awayMap (Hilbert.Polynomial.GradedHilbert.grading K n) hgd rfl) =
        ChartFunctionField.homogeneousChartFunctionFieldMap K f hf := by
  let hu : IsUnit (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (Localization.Away (f * g)) f) :=
    IsLocalization.Away.isUnit_of_dvd (f * g) (dvd_mul_right f g)
  let a : Localization.Away f →+* Localization.Away (f * g) := IsLocalization.Away.lift f hu
  have ha : (ChartFunctionField.localizationFunctionFieldMap K (f * g) (mul_ne_zero hf hg)).comp a =
      ChartFunctionField.localizationFunctionFieldMap K f hf := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro r
    change ChartFunctionField.localizationFunctionFieldMap K (f * g) (mul_ne_zero hf hg)
        (a (algebraMap _ (Localization.Away f) r)) =
      ChartFunctionField.localizationFunctionFieldMap K f hf (algebraMap _ (Localization.Away f) r)
    rw [show a (algebraMap _ (Localization.Away f) r) =
        algebraMap _ (Localization.Away (f * g)) r from IsLocalization.Away.lift_eq f hu r,
      ChartFunctionField.localizationFunctionFieldMap_algebraMap, ChartFunctionField.localizationFunctionFieldMap_algebraMap]
  apply RingHom.ext
  intro z
  change ChartFunctionField.localizationFunctionFieldMap K (f * g) (mul_ne_zero hf hg)
      (HomogeneousLocalization.awayMap (Hilbert.Polynomial.GradedHilbert.grading K n) hgd rfl z).val =
    ChartFunctionField.localizationFunctionFieldMap K f hf z.val
  rw [HomogeneousLocalization.val_awayMap]
  exact RingHom.congr_fun ha z.val

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.FunctionFieldRestrictions
