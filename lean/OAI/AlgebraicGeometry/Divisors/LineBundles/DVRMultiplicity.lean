import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor

/-! # DVR Multiplicity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DVRMultiplicity.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the local order is the actual discrete-valuation exponent

At a codimension-one point whose local ring is a DVR, a nonzero rational
function is a local unit times a power of any chosen uniformizer. The power
is proved to equal the existing Scheme.ord, so it is the same integer used
in the algebraic principal divisor.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

universe u v

/-- The order homomorphism computes the exponent of a uniformizer times a unit. -/
theorem ordFrac_unit_zpow {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π) (u : Rˣ) (m : ℤ) :
    Ring.ordFrac R (u • (algebraMap R K π) ^ m) =
      (Multiplicative.ofAdd m : Multiplicative ℤ) := by
  rw [Units.smul_def, Algebra.smul_def, map_mul, Ring.ordFrac_of_isUnit u.isUnit, one_mul,
    map_zpow₀, Ring.ordFrac_irreducible hπ]
  rw [WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  simp

/-- The DVR factorization theorem with its exponent identified with the
actual algebraic divisor coefficient. -/
theorem rationalFunction_DVR_factorization (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (x : X) (hx : coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (π : X.presheaf.stalk x) (hπ : Irreducible π) (f : X.functionField) (hf : f ≠ 0) :
    ∃ u : (X.presheaf.stalk x)ˣ,
      f = u • (algebraMap (X.presheaf.stalk x) X.functionField π) ^ (X.ord f x) := by
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hf
  have hm : X.ord f x = m := by
    apply (Scheme.ord_eq_iff hx hf).mpr
    change Ring.ordFrac (X.presheaf.stalk x) f = _
    rw [hu]
    exact ordFrac_unit_zpow π hπ u m
  exact ⟨u, hm ▸ hu⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DVRMultiplicity.BundleCycles
