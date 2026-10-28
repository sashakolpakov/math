import OAI.AlgebraicGeometry.Divisors.LineBundles.FractionOrderLaws
import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRMultiplicity

/-! # DVR Unit -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DVRUnit.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual unit part of a DVR rational function

A chosen uniformizer expresses every nonzero rational function as a
unique local unit times the uniformizer to its actual integer order.
The unit is constructed from the DVR factorization theorem, and
uniqueness follows from injection into the fraction field.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)

include hπ

theorem exists_dvrUnitPart (g : Kˣ) :
    ∃ u : Rˣ, (g : K) = u • (algebraMap R K π) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) := by
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ g.ne_zero
  have hm : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) = m := by
    unfold SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder
    rw [hu, DVRMultiplicity.BundleCycles.ordFrac_unit_zpow π hπ u m]
    rfl
  exact ⟨u, hm ▸ hu⟩

def dvrUnitPart (g : Kˣ) : Rˣ := Classical.choose (exists_dvrUnitPart π hπ g)

theorem dvrUnitPart_spec (g : Kˣ) :
    (g : K) = dvrUnitPart π hπ g • (algebraMap R K π) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K) :=
  Classical.choose_spec (exists_dvrUnitPart π hπ g)

theorem dvrUnitPart_unique (g : Kˣ) (u : Rˣ)
    (hu : (g : K) = u • (algebraMap R K π) ^ SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K)) :
    dvrUnitPart π hπ g = u := by
  apply Units.ext
  apply IsFractionRing.injective R K
  have hp : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero
  apply mul_right_cancel₀ (zpow_ne_zero (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K)) hp)
  simpa only [Units.smul_def, Algebra.smul_def] using (dvrUnitPart_spec π hπ g).symm.trans hu

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DVRUnit.BundleCycles
