import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord

/-! # Divisor Laws -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorLaws.BundleCycles

noncomputable section

/-!
# LineBundleCycles: group laws for actual principal-divisor cycles

The existing finite principal-divisor construction is a homomorphism
from nonzero rational functions to integral cycles. Powers and quotients
therefore have the actual integer-multiple and difference divisors.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

universe u
variable (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]

theorem principalDivisor_one : Ord.BundleCycles.principalDivisor X 1 = 0 := by
  ext x
  by_cases hx : coheight x = 1
  · change X.ord 1 x = 0
    rw [X.ord_eq_ordHom_of_coheight_eq_one hx, map_one]
    rfl
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

def principalDivisorHom : X.functionFieldˣ →* Multiplicative (X →₀ ℤ) where
  toFun g := Multiplicative.ofAdd (Ord.BundleCycles.principalDivisor X (g : X.functionField))
  map_one' := congrArg Multiplicative.ofAdd (principalDivisor_one X)
  map_mul' g h := congrArg Multiplicative.ofAdd
    (Ord.BundleCycles.principalDivisor_mul X (g : X.functionField) (h : X.functionField) g.ne_zero h.ne_zero)

theorem principalDivisor_zpow (g : X.functionFieldˣ) (n : ℤ) :
    Ord.BundleCycles.principalDivisor X ((g : X.functionField) ^ n) = n • Ord.BundleCycles.principalDivisor X (g : X.functionField) := by
  have h := congrArg Multiplicative.toAdd (map_zpow (principalDivisorHom X) g n)
  simp only [principalDivisorHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_zpow_eq_zpow_val] at h
  exact h

theorem principalDivisor_div (g h : X.functionFieldˣ) :
    Ord.BundleCycles.principalDivisor X ((g : X.functionField) / (h : X.functionField)) =
      Ord.BundleCycles.principalDivisor X (g : X.functionField) - Ord.BundleCycles.principalDivisor X (h : X.functionField) := by
  have he := congrArg Multiplicative.toAdd (map_div (principalDivisorHom X) g h)
  simp only [principalDivisorHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_div_eq_div_val] at he
  exact he

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorLaws.BundleCycles
