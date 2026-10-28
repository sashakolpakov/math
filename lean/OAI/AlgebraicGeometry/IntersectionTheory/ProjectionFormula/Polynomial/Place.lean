import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BranchOrder
import Mathlib.RingTheory.Polynomial.Quotient

/-! # Place -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place

noncomputable section

/-! The zero place of a rational parameter: its local ring is a DVR,
the parameter has order one, and its residue field is the ground field. -/

open UniqueFactorizationMonoid

variable (k : Type*) [Field k]

def zeroIdeal : Ideal (Polynomial k) := Ideal.span {Polynomial.X}

instance : (zeroIdeal k).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X

theorem zeroIdeal_ne_bot : zeroIdeal k ≠ ⊥ :=
  Ideal.span_singleton_eq_bot.not.mpr Polynomial.X_ne_zero

abbrev localRing := Localization.AtPrime (zeroIdeal k)

instance : IsDiscreteValuationRing (localRing k) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial k) (zeroIdeal_ne_bot k) _

def parameter : FractionRing (Polynomial k) := algebraMap (Polynomial k) _ Polynomial.X

theorem parameter_ne_zero : parameter k ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (FractionRing (Polynomial k)))).mpr
    Polynomial.X_ne_zero

theorem order_parameter : WithZero.log (Ring.ordFrac (localRing k) (parameter k)) = 1 := by
  classical
  have hp : Prime (zeroIdeal k) := Ideal.prime_of_isPrime (zeroIdeal_ne_bot k) inferInstance
  have ho : Ring.ord (localRing k) (algebraMap (Polynomial k) (localRing k) Polynomial.X) = 1 := by
    rw [BranchOrder.ord_eq_count (zeroIdeal k) (zeroIdeal_ne_bot k) Polynomial.X Polynomial.X_ne_zero]
    change ((normalizedFactors (zeroIdeal k)).count (zeroIdeal k) : ℕ∞) = 1
    rw [normalizedFactors_irreducible hp.irreducible]
    simp
  have hx : algebraMap (Polynomial k) (localRing k) Polynomial.X ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective (localRing k)
      (zeroIdeal k).primeCompl_le_nonZeroDivisors)).mpr Polynomial.X_ne_zero
  rw [parameter, IsScalarTower.algebraMap_apply (Polynomial k) (localRing k) (FractionRing (Polynomial k)),
    Ring.ordFrac_eq_ord (localRing k) hx,
    Ring.ordMonoidWithZeroHom_eq_coe (localRing k) (mem_nonZeroDivisors_of_ne_zero hx) ho]
  rfl

theorem order_parameter_pow (n : ℕ) :
    WithZero.log (Ring.ordFrac (localRing k) (parameter k ^ n)) = n := by
  rw [map_pow, WithZero.log_pow, order_parameter]
  simp

def quotientEquiv : (Polynomial k ⧸ zeroIdeal k) ≃ₐ[k] k := by
  have h : zeroIdeal k = Ideal.span {Polynomial.X - Polynomial.C (0 : k)} := by simp [zeroIdeal]
  exact (Ideal.quotientEquivAlgOfEq k h).trans (Polynomial.quotientSpanXSubCAlgEquiv (0 : k))

def residueEquiv : (zeroIdeal k).ResidueField ≃ₐ[k] k := by
  let Q := Polynomial k ⧸ zeroIdeal k
  let : Field Q := (MulEquiv.isField (Field.toIsField k) (quotientEquiv k).toMulEquiv).toField
  let e : Q ≃ₐ[Q] (zeroIdeal k).ResidueField := IsFractionRing.algEquiv Q Q (zeroIdeal k).ResidueField
  exact (e.symm.restrictScalars k).trans (quotientEquiv k)

theorem residue_finrank : Module.finrank k (zeroIdeal k).ResidueField = 1 := by
  rw [(residueEquiv k).toLinearEquiv.finrank_eq, Module.finrank_self]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place
