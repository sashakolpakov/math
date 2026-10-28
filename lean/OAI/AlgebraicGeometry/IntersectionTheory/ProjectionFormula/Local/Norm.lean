import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Norm -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Norm

noncomputable section

/-!
# ProjectionFormula: local norm and divisor multiplicities

For a finite local extension of discrete valuation rings in characteristic
zero (more generally with perfect fraction field), the order of a norm is
the residue-field degree times the source order. This is the local numerical
identity needed when pushing principal divisors through a finite map.
-/

open IsLocalRing IsDiscreteValuationRing

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [IsLocalHom (algebraMap R S)] [PerfectField (FractionRing R)]

/-- The norm of a uniformizer has order the residue-field extension degree. -/
theorem ord_intNorm_uniformizer (π : S) (hπ : Irreducible π) :
    Ring.ord R (Algebra.intNorm R S π) = ((IsLocalRing.maximalIdeal S).inertiaDeg R : ℕ∞) := by
  have hI : Ideal.span {Algebra.intNorm R S π} =
      IsLocalRing.maximalIdeal R ^ (IsLocalRing.maximalIdeal S).inertiaDeg R := by
    rw [← Ideal.relNorm_singleton, ← hπ.maximalIdeal_eq]
    exact Ideal.relNorm_eq_pow_of_isMaximal
      (IsLocalRing.maximalIdeal S) (IsLocalRing.maximalIdeal R)
  change Module.length R (R ⧸ Ideal.span {Algebra.intNorm R S π}) = _
  rw [hI, length_quotient_pow_maximalIdeal]

/-- The actual norm multiplies orders by the residue degree. -/
theorem ord_intNorm (a : S) (ha : a ≠ 0) :
    Ring.ord R (Algebra.intNorm R S a) =
      ((IsLocalRing.maximalIdeal S).inertiaDeg R : ℕ∞) * Ring.ord S a := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  obtain ⟨k, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
  rw [map_mul, map_pow, Ring.ord_mul_of_isUnit_left (u.isUnit.map (Algebra.intNorm R S)),
    Ring.ord_pow, ord_intNorm_uniformizer π hπ,
    Ring.ord_mul_of_isUnit_left u.isUnit, Ring.ord_pow, Ring.ord_of_irreducible hπ]
  · simp [nsmul_eq_mul, mul_comm]
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero
  · exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (Algebra.intNorm_ne_zero.mpr hπ.ne_zero)

/-- The multiplier above is the native degree of the residue-field extension. -/
theorem ord_intNorm_residueDegree (a : S) (ha : a ≠ 0) :
    Ring.ord R (Algebra.intNorm R S a) =
      (Module.finrank (ResidueField R) (ResidueField S) : ℕ∞) * Ring.ord S a := by
  rw [ord_intNorm a ha, Ideal.inertiaDeg_eq_of_isMaximal
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)]
  rfl

attribute [local instance] FractionRing.liftAlgebra

/-- The corresponding fraction-field order of the norm of a uniformizer. -/
theorem ordFrac_norm_uniformizer (π : S) (hπ : Irreducible π) :
    Ring.ordFrac R (Algebra.norm (FractionRing R)
      (algebraMap S (FractionRing S) π)) =
        WithZero.exp ((IsLocalRing.maximalIdeal S).inertiaDeg R : ℤ) := by
  rw [← Algebra.algebraMap_intNorm_fractionRing]
  rw [Ring.ordFrac_eq_ord R (Algebra.intNorm_ne_zero.mpr hπ.ne_zero)]
  exact Ring.ordMonoidWithZeroHom_eq_coe R
    (mem_nonZeroDivisors_iff_ne_zero.mpr (Algebra.intNorm_ne_zero.mpr hπ.ne_zero))
    (ord_intNorm_uniformizer π hπ)

/-- Norm and order for arbitrary nonzero rational functions in the local
fraction fields; negative orders are included through integer powers. -/
theorem ordFrac_norm (a : FractionRing S) (ha : a ≠ 0) :
    Ring.ordFrac R (Algebra.norm (FractionRing R) a) =
      (Ring.ordFrac S a) ^ (IsLocalRing.maximalIdeal S).inertiaDeg R := by
  obtain ⟨π, hπ⟩ := exists_irreducible S
  obtain ⟨k, u, rfl⟩ := exists_units_eq_smul_zpow_of_irreducible hπ ha
  rw [Units.smul_def, Algebra.smul_def, map_mul, Algebra.norm_zpow,
    ← Algebra.algebraMap_intNorm_fractionRing, map_mul, map_zpow₀,
    Ring.ordFrac_of_isUnit (u.isUnit.map (Algebra.intNorm R S)),
    ordFrac_norm_uniformizer π hπ, one_mul]
  rw [map_mul, map_zpow₀, Ring.ordFrac_of_isUnit u.isUnit,
    Ring.ordFrac_irreducible hπ, one_mul]
  simp only [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, zsmul_eq_mul,
    nsmul_eq_mul, mul_one, mul_comm]

/-- Additive integer-valued form of the local norm formula. -/
theorem log_ordFrac_norm (a : FractionRing S) (ha : a ≠ 0) :
    WithZero.log (Ring.ordFrac R (Algebra.norm (FractionRing R) a)) =
      ((IsLocalRing.maximalIdeal S).inertiaDeg R : ℤ) *
        WithZero.log (Ring.ordFrac S a) := by
  rw [ordFrac_norm a ha, WithZero.log_pow]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Norm
