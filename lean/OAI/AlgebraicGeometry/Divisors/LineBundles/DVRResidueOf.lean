import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRUnit
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-! # DVR Residue Of -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueOf.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: multiplicative unit parts and their actual residues

Uniqueness of the DVR factorization makes the unit part multiplicative.
Reducing these local units through the actual residue-field homomorphism
then gives the multiplicative residue map used in the common-component
symbol.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)

theorem dvrUnitPart_one : DVRUnit.BundleCycles.dvrUnitPart (K := K) π hπ 1 = 1 := by
  apply DVRUnit.BundleCycles.dvrUnitPart_unique
  change (1 : K) = (1 : Rˣ) • (algebraMap R K π) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (1 : K)
  rw [FractionOrderLaws.BundleCycles.fractionFieldOrder_one R]
  simp

theorem dvrUnitPart_mul (g h : Kˣ) :
    DVRUnit.BundleCycles.dvrUnitPart π hπ (g * h) = DVRUnit.BundleCycles.dvrUnitPart π hπ g * DVRUnit.BundleCycles.dvrUnitPart π hπ h := by
  have hp : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero
  apply DVRUnit.BundleCycles.dvrUnitPart_unique
  change (g : K) * (h : K) =
    (DVRUnit.BundleCycles.dvrUnitPart π hπ g * DVRUnit.BundleCycles.dvrUnitPart π hπ h) •
      (algebraMap R K π) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R ((g : K) * (h : K))
  rw [FractionOrderLaws.BundleCycles.fractionFieldOrder_mul R (g : K) (h : K) g.ne_zero h.ne_zero]
  refine (congrArg₂ (· * ·) (DVRUnit.BundleCycles.dvrUnitPart_spec π hπ g) (DVRUnit.BundleCycles.dvrUnitPart_spec π hπ h)).trans ?_
  simp only [Units.smul_def, Algebra.smul_def, Units.val_mul, map_mul, zpow_add₀ hp]
  ring

def dvrUnitPartHom : Kˣ →* Rˣ where
  toFun := DVRUnit.BundleCycles.dvrUnitPart π hπ
  map_one' := dvrUnitPart_one π hπ
  map_mul' := dvrUnitPart_mul π hπ

/-- The actual residue of the unit factor, as a unit in the residue field. -/
def dvrUnitResidueHom : Kˣ →* (IsLocalRing.ResidueField R)ˣ :=
  (Units.map (IsLocalRing.residue R)).comp (dvrUnitPartHom π hπ)

end

section

/-!
# LineBundleCycles: the residue quotient for two rational functions on a DVR

The quotient of unit parts to the opposite orders is an actual local
unit. Its fraction-field image is g^ord(h)/h^ord(g), whose uniformizer
powers cancel. This characterizes it independently of the chosen
uniformizer; reduction gives the corresponding actual residue-field unit.
The conventional tame-symbol sign is unnecessary for its principal divisor.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)

def dvrBalancedUnit (g h : Kˣ) : Rˣ :=
  (DVRUnit.BundleCycles.dvrUnitPart π hπ g) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (h : K) /
    (DVRUnit.BundleCycles.dvrUnitPart π hπ h) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K)

theorem dvrBalancedUnit_fraction (g h : Kˣ) :
    algebraMap R K (dvrBalancedUnit π hπ g h : R) =
      (g : K) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (h : K) / (h : K) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) := by
  have hp : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero
  have he := congrArg₂ (fun x y : K => x ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (h : K) /
    y ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K)) (DVRUnit.BundleCycles.dvrUnitPart_spec π hπ g) (DVRUnit.BundleCycles.dvrUnitPart_spec π hπ h)
  refine Eq.trans ?_ he.symm
  change ((Units.map (algebraMap R K).toMonoidHom (dvrBalancedUnit π hπ g h) : Kˣ) : K) = _
  rw [dvrBalancedUnit, map_div, map_zpow, map_zpow]
  simp only [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, Units.coe_map,
    Units.smul_def, Algebra.smul_def, mul_zpow, ← zpow_mul]
  rw [mul_comm (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K)) (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (h : K))]
  exact (mul_div_mul_right _ _ (zpow_ne_zero _ hp)).symm

theorem dvrBalancedUnit_independent (ρ : R) (hρ : Irreducible ρ) (g h : Kˣ) :
    dvrBalancedUnit π hπ g h = dvrBalancedUnit ρ hρ g h := by
  apply Units.ext
  apply IsFractionRing.injective R K
  exact (dvrBalancedUnit_fraction π hπ g h).trans (dvrBalancedUnit_fraction ρ hρ g h).symm

/-- The actual residue-field unit used for the common-component rational function. -/
def dvrResidueQuotient (g h : Kˣ) : (IsLocalRing.ResidueField R)ˣ :=
  Units.map (IsLocalRing.residue R).toMonoidHom (dvrBalancedUnit π hπ g h)

theorem dvrResidueQuotient_independent (ρ : R) (hρ : Irreducible ρ) (g h : Kˣ) :
    dvrResidueQuotient π hπ g h = dvrResidueQuotient ρ hρ g h :=
  congrArg (Units.map (IsLocalRing.residue R).toMonoidHom) (dvrBalancedUnit_independent π hπ ρ hρ g h)

end

/-!
# LineBundleCycles: residue quotients from actual uniformizer factorizations

The order and the unit part are derived from the exhibited factorization.
Reducing the resulting balanced unit gives the actual residue quotient.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)

include hπ

theorem fractionFieldOrder_of_unit_zpow (g : Kˣ) (u : Rˣ) (m : ℤ)
    (hg : (g : K) = u • (algebraMap R K π) ^ m) : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) = m := by
  unfold SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder
  rw [hg, DVRMultiplicity.BundleCycles.ordFrac_unit_zpow π hπ u m]
  rfl

theorem dvrUnitPart_of_unit_zpow (g : Kˣ) (u : Rˣ) (m : ℤ)
    (hg : (g : K) = u • (algebraMap R K π) ^ m) : DVRUnit.BundleCycles.dvrUnitPart π hπ g = u := by
  apply DVRUnit.BundleCycles.dvrUnitPart_unique π hπ g u
  rw [fractionFieldOrder_of_unit_zpow π hπ g u m hg]
  exact hg

theorem dvrBalancedUnit_of_factors (g h : Kˣ) (u v : Rˣ) (m n : ℤ)
    (hg : (g : K) = u • (algebraMap R K π) ^ m)
    (hh : (h : K) = v • (algebraMap R K π) ^ n) :
    dvrBalancedUnit π hπ g h = u ^ n / v ^ m := by
  rw [dvrBalancedUnit, dvrUnitPart_of_unit_zpow π hπ g u m hg,
    dvrUnitPart_of_unit_zpow π hπ h v n hh,
    fractionFieldOrder_of_unit_zpow π hπ g u m hg,
    fractionFieldOrder_of_unit_zpow π hπ h v n hh]

theorem dvrResidueQuotient_of_factors (g h : Kˣ) (u v : Rˣ) (m n : ℤ)
    (hg : (g : K) = u • (algebraMap R K π) ^ m)
    (hh : (h : K) = v • (algebraMap R K π) ^ n) :
    dvrResidueQuotient π hπ g h =
      (Units.map (IsLocalRing.residue R).toMonoidHom u) ^ n /
        (Units.map (IsLocalRing.residue R).toMonoidHom v) ^ m := by
  rw [dvrResidueQuotient, dvrBalancedUnit_of_factors π hπ g h u v m n hg hh,
    map_div, map_zpow, map_zpow]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueOf.BundleCycles
