import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! # Regular Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularOrder.Constructions

noncomputable section

/-! The scheme order of a nonzero regular germ is the finite length
of its actual principal quotient, with the same integer normalization. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem ord_algebraMap_stalk (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : Order.coheight x = 1) (r : X.presheaf.stalk x) (hr : r ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField r) x =
      ((Ring.ord (X.presheaf.stalk x) r).toNat : ℤ) := by
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hn : Ring.ord (X.presheaf.stalk x) r =
      ((Ring.ord (X.presheaf.stalk x) r).toNat : ℕ∞) :=
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hr))).symm
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  change Multiplicative.toAdd ((Ring.ordFrac (X.presheaf.stalk x)
    (algebraMap (X.presheaf.stalk x) X.functionField r)).unzeroD 1) = _
  rw [Ring.ordFrac_eq_ord _ hr,
    Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hr) hn]
  rfl

theorem ord_germToFunctionField (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (hx : Order.coheight x = 1) (U : X.Opens) [Nonempty U] (hxU : x ∈ U)
    (r : Γ(X, U)) (hr : r ≠ 0) :
    X.ord (X.germToFunctionField U r) x =
      ((Ring.ord (X.presheaf.stalk x) (X.presheaf.germ U x hxU r)).toNat : ℤ) := by
  rw [← X.algebraMap_germ_eq_germToFunctionField hxU r]
  exact ord_algebraMap_stalk X x hx _
    ((map_ne_zero_iff _ (germ_injective_of_isIntegral X x hxU)).mpr hr)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularOrder.Constructions
