import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueOf

/-! # DVR Residue Regular Steinberg -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueRegularSteinberg.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: residue quotient laws and the proper-component case

The actual residue quotient is multiplicative in each argument and
inverts when the arguments are exchanged. If the first rational
function is already a local unit, its residue quotient is simply its
residue raised to the second function's actual order.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)

theorem dvrBalancedUnit_swap (g h : Kˣ) :
    DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ h g = (DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ g h)⁻¹ := by
  unfold DVRResidueOf.BundleCycles.dvrBalancedUnit
  rw [inv_div]

theorem dvrBalancedUnit_mul_left (g h k : Kˣ) :
    DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ (g * h) k = DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ g k * DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ h k := by
  simp only [DVRResidueOf.BundleCycles.dvrBalancedUnit, DVRResidueOf.BundleCycles.dvrUnitPart_mul, Units.val_mul,
    FractionOrderLaws.BundleCycles.fractionFieldOrder_mul R (g : K) (h : K) g.ne_zero h.ne_zero, mul_zpow]
  rw [zpow_add]
  exact (div_mul_div_comm _ _ _ _).symm

theorem dvrBalancedUnit_mul_right (g h k : Kˣ) :
    DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ g (h * k) = DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ g h * DVRResidueOf.BundleCycles.dvrBalancedUnit π hπ g k := by
  simp only [DVRResidueOf.BundleCycles.dvrBalancedUnit, DVRResidueOf.BundleCycles.dvrUnitPart_mul, Units.val_mul,
    FractionOrderLaws.BundleCycles.fractionFieldOrder_mul R (h : K) (k : K) h.ne_zero k.ne_zero, mul_zpow]
  rw [zpow_add]
  exact (div_mul_div_comm _ _ _ _).symm

theorem dvrResidueQuotient_mul_left (g h k : Kˣ) :
    DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ (g * h) k = DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g k * DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ h k := by
  unfold DVRResidueOf.BundleCycles.dvrResidueQuotient
  rw [dvrBalancedUnit_mul_left, map_mul]

theorem dvrResidueQuotient_mul_right (g h k : Kˣ) :
    DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g (h * k) = DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h * DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g k := by
  unfold DVRResidueOf.BundleCycles.dvrResidueQuotient
  rw [dvrBalancedUnit_mul_right, map_mul]

theorem dvrResidueQuotient_swap (g h : Kˣ) :
    DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ h g = (DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h)⁻¹ := by
  unfold DVRResidueOf.BundleCycles.dvrResidueQuotient
  rw [dvrBalancedUnit_swap, map_inv]

theorem fractionFieldOrder_localUnit (u : Rˣ) : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (algebraMap R K u) = 0 := by
  unfold SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder
  rw [Ring.ordFrac_of_isUnit u.isUnit]
  rfl

theorem dvrUnitPart_localUnit (u : Rˣ) :
    DVRUnit.BundleCycles.dvrUnitPart π hπ (Units.map (algebraMap R K).toMonoidHom u) = u := by
  apply DVRUnit.BundleCycles.dvrUnitPart_unique
  change algebraMap R K (u : R) = u • (algebraMap R K π) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (algebraMap R K u)
  rw [fractionFieldOrder_localUnit, zpow_zero]
  simp only [Units.smul_def, Algebra.smul_def, mul_one]

/-- On a proper component the residue quotient recovers the ordinary restricted rational function. -/
theorem dvrResidueQuotient_localUnit (u : Rˣ) (h : Kˣ) :
    DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ (Units.map (algebraMap R K).toMonoidHom u) h =
      (Units.map (IsLocalRing.residue R).toMonoidHom u) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (h : K) := by
  unfold DVRResidueOf.BundleCycles.dvrResidueQuotient DVRResidueOf.BundleCycles.dvrBalancedUnit
  rw [dvrUnitPart_localUnit]
  change Units.map (IsLocalRing.residue R).toMonoidHom
    (u ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (h : K) /
      DVRUnit.BundleCycles.dvrUnitPart π hπ h ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (algebraMap R K u)) = _
  rw [fractionFieldOrder_localUnit, zpow_zero, div_one, map_zpow]

end

section

/-!
# LineBundleCycles: actual regular representatives from nonnegative local order

The unit/uniformizer factorization constructs a local-ring representative
of a rational function of nonnegative order. Positive order forces its
residue to vanish. These are used in the residue-symbol relations.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)

include π hπ

theorem dvr_exists_regularRepresentative (g : Kˣ) (hg : 0 ≤ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K)) :
    ∃ a : R, algebraMap R K a = g := by
  let n := (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K)).toNat
  have hn : (n : ℤ) = SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) := Int.toNat_of_nonneg hg
  refine ⟨(DVRUnit.BundleCycles.dvrUnitPart π hπ g : R) * π ^ n, ?_⟩
  have hs := DVRUnit.BundleCycles.dvrUnitPart_spec π hπ g
  rw [← hn, zpow_natCast] at hs
  simpa only [map_mul, map_pow, Units.smul_def, Algebra.smul_def] using hs.symm

theorem dvr_uniformizer_residue : IsLocalRing.residue R π = 0 :=
  (IsLocalRing.residue_eq_zero_iff π).mpr hπ.not_isUnit

theorem dvr_regularRepresentative_residue_zero (g : Kˣ)
    (hg : 0 < SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K)) (a : R) (ha : algebraMap R K a = g) :
    IsLocalRing.residue R a = 0 := by
  let n := (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K)).toNat
  have hn : (n : ℤ) = SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) := Int.toNat_of_nonneg hg.le
  have hnpos : n ≠ 0 := by omega
  have he : a = (DVRUnit.BundleCycles.dvrUnitPart π hπ g : R) * π ^ n := by
    apply IsFractionRing.injective R K
    rw [ha]
    have hs := DVRUnit.BundleCycles.dvrUnitPart_spec π hπ g
    rw [← hn, zpow_natCast] at hs
    simpa only [map_mul, map_pow, Units.smul_def, Algebra.smul_def] using hs
  rw [he, map_mul, map_pow, dvr_uniformizer_residue π hπ, zero_pow hnpos, mul_zero]

theorem dvrUnitPart_of_order_zero (g : Kˣ) (hg : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) = 0) :
    algebraMap R K (DVRUnit.BundleCycles.dvrUnitPart π hπ g : R) = g := by
  have hs := DVRUnit.BundleCycles.dvrUnitPart_spec π hπ g
  rw [hg, zpow_zero] at hs
  simpa only [Units.smul_def, Algebra.smul_def, mul_one] using hs.symm

end

section

/-!
# LineBundleCycles: the actual residue quotient is a homomorphism in either argument

This packages the checked product laws so inverses and quotients can be
used directly when reducing common-component symbol identities.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)

theorem dvrResidueQuotient_self (g : Kˣ) : DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g g = 1 := by
  unfold DVRResidueOf.BundleCycles.dvrResidueQuotient DVRResidueOf.BundleCycles.dvrBalancedUnit
  simp

theorem dvrResidueQuotient_one_left (g : Kˣ) : DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ 1 g = 1 := by
  unfold DVRResidueOf.BundleCycles.dvrResidueQuotient DVRResidueOf.BundleCycles.dvrBalancedUnit
  simp only [DVRResidueOf.BundleCycles.dvrUnitPart_one, one_zpow, Units.val_one, FractionOrderLaws.BundleCycles.fractionFieldOrder_one,
    zpow_zero, div_one, map_one]

theorem dvrResidueQuotient_one_right (g : Kˣ) : DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g 1 = 1 := by
  rw [dvrResidueQuotient_swap, dvrResidueQuotient_one_left, inv_one]

def dvrResidueQuotientLeftHom (h : Kˣ) : Kˣ →* (IsLocalRing.ResidueField R)ˣ where
  toFun g := DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h
  map_one' := dvrResidueQuotient_one_left π hπ h
  map_mul' g k := dvrResidueQuotient_mul_left π hπ g k h

def dvrResidueQuotientRightHom (g : Kˣ) : Kˣ →* (IsLocalRing.ResidueField R)ˣ where
  toFun h := DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h
  map_one' := dvrResidueQuotient_one_right π hπ g
  map_mul' h k := dvrResidueQuotient_mul_right π hπ g h k

theorem dvrResidueQuotient_inv_left (g h : Kˣ) :
    DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g⁻¹ h = (DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h)⁻¹ :=
  map_inv (dvrResidueQuotientLeftHom π hπ h) g

theorem dvrResidueQuotient_div_right (g h k : Kˣ) :
    DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g (h / k) =
      DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h / DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g k :=
  map_div (dvrResidueQuotientRightHom π hπ g) h k

end

section

/-!
# LineBundleCycles: the Steinberg residue identity for actual regular representatives

If two nonzero regular functions add to one, one is a local unit. Their
actual residue quotient is one, by reducing the equation in the residue
field. This is the regular case of the symbol relation used in reciprocity.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)

theorem dvrResidueQuotient_unit_add_one (u : Rˣ) (a : R) (h : Kˣ)
    (ha : algebraMap R K a = h) (hsum : (u : R) + a = 1) :
    DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ (Units.map (algebraMap R K).toMonoidHom u) h = 1 := by
  rw [dvrResidueQuotient_localUnit]
  by_cases hu : IsUnit a
  · obtain ⟨v, hv⟩ := hu
    have ho : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (h : K) = 0 := by
      rw [← ha, ← hv]
      exact fractionFieldOrder_localUnit v
    rw [ho, zpow_zero]
  · have hz : IsLocalRing.residue R a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr hu
    have hr : Units.map (IsLocalRing.residue R).toMonoidHom u = 1 := by
      apply Units.ext
      change IsLocalRing.residue R (u : R) = 1
      have he := congrArg (IsLocalRing.residue R) hsum
      simpa only [map_add, map_one, hz, add_zero] using he
    rw [hr, one_zpow]

theorem dvrResidueQuotient_regular_add_one (g h : Kˣ) (a b : R)
    (ha : algebraMap R K a = g) (hb : algebraMap R K b = h)
    (hsum : (g : K) + (h : K) = 1) : DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h = 1 := by
  have hab : a + b = 1 := by
    apply IsFractionRing.injective R K
    rw [map_add, map_one, ha, hb, hsum]
  have hu : IsUnit (a + b) := hab.symm ▸ isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with hau | hbu
  · obtain ⟨u, hu⟩ := hau
    have hg : g = Units.map (algebraMap R K).toMonoidHom u :=
      Units.ext ((congrArg (algebraMap R K) hu).trans ha).symm
    rw [hg]
    exact dvrResidueQuotient_unit_add_one π hπ u b h hb (hu.symm ▸ hab)
  · obtain ⟨u, hu⟩ := hbu
    have hh : h = Units.map (algebraMap R K).toMonoidHom u :=
      Units.ext ((congrArg (algebraMap R K) hu).trans hb).symm
    rw [dvrResidueQuotient_swap, hh,
      dvrResidueQuotient_unit_add_one π hπ u a g ha (by rw [hu, add_comm, hab]), inv_one]

end

/-!
# LineBundleCycles: the residue quotient for a Steinberg pair, including poles

For g+h=1 the unsigned residue quotient is one when g is regular.
For a pole, invert g to reduce to the regular case; the result is the
residue of -1 raised to the actual order of g. In either case this is a
constant sign, which has zero principal divisor on the geometric support.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)

theorem dvrResidueQuotient_add_one_of_nonneg (g h : Kˣ)
    (hsum : (g : K) + (h : K) = 1) (hg : 0 ≤ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K)) :
    DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h = 1 := by
  obtain ⟨a, ha⟩ := dvr_exists_regularRepresentative π hπ g hg
  have hb : algebraMap R K (1 - a) = h := by
    rw [map_sub, map_one, ha]
    exact sub_eq_iff_eq_add.mpr (hsum.symm.trans (add_comm _ _))
  exact dvrResidueQuotient_regular_add_one π hπ g h a (1 - a) ha hb hsum

theorem dvrResidueQuotient_add_one_of_neg (g h : Kˣ)
    (hsum : (g : K) + (h : K) = 1) (hg : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) < 0) :
    DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h =
      (Units.map (IsLocalRing.residue R).toMonoidHom (-1 : Rˣ)) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) := by
  let w := Units.map (algebraMap R K).toMonoidHom (-1 : Rˣ)
  let k := w * h / g
  have hinv : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R ((g⁻¹ : Kˣ) : K) = -SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) :=
    congrArg Multiplicative.toAdd (map_inv (FractionOrderLaws.BundleCycles.fractionFieldOrderHom (K := K) R) g)
  have hw : (w : K) = -1 := by
    change algebraMap R K (-1) = -1
    rw [map_neg, map_one]
  have hsum' : ((g⁻¹ : Kˣ) : K) + (k : K) = 1 := by
    simp only [k, Units.val_inv_eq_inv_val, Units.val_div_eq_div_val, Units.val_mul, hw]
    field_simp
    linear_combination -hsum
  have hz := dvrResidueQuotient_add_one_of_nonneg π hπ g⁻¹ k hsum' (by rw [hinv]; omega)
  rw [dvrResidueQuotient_inv_left, inv_eq_one] at hz
  change DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g (w * h / g) = 1 at hz
  rw [dvrResidueQuotient_div_right, dvrResidueQuotient_mul_right,
    dvrResidueQuotient_self, div_one] at hz
  rw [dvrResidueQuotient_swap π hπ w g, dvrResidueQuotient_localUnit] at hz
  exact (inv_mul_eq_one.mp hz).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueRegularSteinberg.BundleCycles
