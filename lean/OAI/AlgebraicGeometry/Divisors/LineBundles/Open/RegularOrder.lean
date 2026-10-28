import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor

/-! # Regular Order -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RegularOrder.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual regular germs on arbitrary open neighborhoods have nonnegative local-length orders -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U] (a : Γ(X, U))

theorem openRegular_order_length (ha : a ≠ 0) (x : X) (hxU : x ∈ U) (hx : coheight x = 1) :
    X.ord (X.germToFunctionField U a) x =
      ((Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ U x hxU a})).toNat : ℤ) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hg : X.presheaf.germ U x hxU a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral X x hxU)).mpr ha
  have hf : X.germToFunctionField U a ≠ 0 :=
    (map_ne_zero_iff _ (X.germToFunctionField_injective U)).mpr ha
  apply (Scheme.ord_eq_iff hx hf).mpr
  change Ring.ordFrac (X.presheaf.stalk x) (X.germToFunctionField U a) = _
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (x := x) hxU a,
    Ring.ordFrac_eq_ord (X.presheaf.stalk x) hg]
  apply Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
  exact (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hg))).symm

theorem openRegular_order_nonnegative (ha : a ≠ 0) (x : X) (hxU : x ∈ U) :
    0 ≤ X.ord (X.germToFunctionField U a) x := by
  by_cases hx : coheight x = 1
  · rw [openRegular_order_length U a ha x hxU hx]
    exact Int.natCast_nonneg _
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx]

theorem openRegular_order_zero_of_isUnit_germ (x : X) (hxU : x ∈ U)
    (ha : IsUnit (X.presheaf.germ U x hxU a)) : X.ord (X.germToFunctionField U a) x = 0 := by
  by_cases hx : coheight x = 1
  · have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    have hf : X.germToFunctionField U a ≠ 0 := by
      rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (x := x) hxU a]
      exact (ha.map (algebraMap _ X.functionField)).ne_zero
    apply (Scheme.ord_eq_iff hx hf).mpr
    change Ring.ordFrac (X.presheaf.stalk x) (X.germToFunctionField U a) = 1
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (x := x) hxU a]
    exact Ring.ordFrac_of_isUnit ha
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RegularOrder.BundleCycles
