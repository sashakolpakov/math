import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceRationalOrderIntersection

/-! # Fraction Order Laws -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FractionOrderLaws.BundleCycles

noncomputable section

/-!
# LineBundleCycles: integer laws for the actual fraction-field order

The integer order uses the same nonzero value of the existing order
homomorphism. Its multiplicative and inverse laws are derived from
that homomorphism, supplying the exponents in the DVR residue symbol.
-/

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem ordFrac_eq_fractionFieldOrder (g : K) (hg : g ≠ 0) :
    Ring.ordFrac R g = ((Multiplicative.ofAdd (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R g) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) := by
  have hn : Ring.ordFrac R g ≠ 0 := (map_ne_zero (Ring.ordFrac R (K := K))).mpr hg
  unfold SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder
  cases h : Ring.ordFrac R g with
  | zero => exact False.elim (hn h)
  | coe z => rfl

theorem fractionFieldOrder_mul (g h : K) (hg : g ≠ 0) (hh : h ≠ 0) :
    SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g * h) = SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R g + SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R h := by
  have he : ((Multiplicative.ofAdd (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g * h)) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R g + SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R h) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [← ordFrac_eq_fractionFieldOrder R (g * h) (mul_ne_zero hg hh), map_mul,
      ordFrac_eq_fractionFieldOrder R g hg, ordFrac_eq_fractionFieldOrder R h hh]
    rfl
  exact congrArg Multiplicative.toAdd (WithZero.coe_inj.mp he)

theorem fractionFieldOrder_one : SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (1 : K) = 0 := by
  unfold SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder
  rw [map_one]
  rfl

def fractionFieldOrderHom : Kˣ →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R (g : K))
  map_one' := congrArg Multiplicative.ofAdd (fractionFieldOrder_one (K := K) R)
  map_mul' g h := congrArg Multiplicative.ofAdd
    (fractionFieldOrder_mul (K := K) R (g : K) (h : K) g.ne_zero h.ne_zero)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FractionOrderLaws.BundleCycles
