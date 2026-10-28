import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Divisor Inverse -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorInverse.BundleCycles.PrincipalDivisorInverse

noncomputable section

/-! Inverting a rational function negates its actual principal divisor,
including the library's zero-function convention. -/

open _root_.AlgebraicGeometry _root_.Order

universe u

variable (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem ord_inv (g : X.functionField) (x : X) : X.ord g⁻¹ x = -X.ord g x := by
  by_cases hx : coheight x = 1
  · let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx, Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
    change WithZero.log (Ring.ordFrac (X.presheaf.stalk x) g⁻¹) =
      -WithZero.log (Ring.ordFrac (X.presheaf.stalk x) g)
    rw [map_inv₀, WithZero.log_inv]
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one hx, neg_zero]

theorem rationalPrincipalPointDivisor_inv (g : X.functionField) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g⁻¹ =
      -RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g := by
  ext x
  change (X.ord g⁻¹ x : ℚ) = -(X.ord g x : ℚ)
  rw [ord_inv, Int.cast_neg]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorInverse.BundleCycles.PrincipalDivisorInverse
