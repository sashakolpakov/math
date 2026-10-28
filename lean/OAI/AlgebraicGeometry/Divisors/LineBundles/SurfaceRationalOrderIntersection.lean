import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceIntersectionFormula
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Surface Rational Order Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceRationalOrderIntersection.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: symmetry of the actual local surface intersection sums

The sum of local divisor multiplicity times quotient length agrees in
both orders. This follows from the proved formula and the actual snake
boundary symmetry. The multiplicities also agree definitionally with
the local ring order, and their finiteness follows from a constructed
prime filtration.
-/

variable {R : Type*} [CommRing R]

theorem primeEquationMultiplicity_eq_ord (b : R) (P : Ideal R) (hP : P.IsPrime) :
    letI : P.IsPrime := hP
    LocalizedEquationLength.BundleCycles.primeEquationMultiplicity b P hP =
      (Ring.ord (Localization P.primeCompl) (algebraMap R (Localization P.primeCompl) b)).toNat := rfl

variable [IsNoetherianRing R]

theorem primeEquation_ord_ne_top (b : R) (P : Ideal R)
    (hP : P ∈ (Ideal.span {b}).minimalPrimes) :
    letI : P.IsPrime := hP.isPrime
    Ring.ord (Localization P.primeCompl) (algebraMap R (Localization P.primeCompl) b) ≠ ⊤ := by
  let : P.IsPrime := hP.isPrime
  let F := PrimeFiltration.BundleCycles.modulePrimeFiltration (R := R) (M := MultiplicationSequence.BundleCycles.equationCokernel b R)
  have h := F.whole_localized_length_eq_count b (LocalIntersectionLength.BundleCycles.equationCokernel_annihilated b R) P hP
  rw [(LocalizedEquationLength.BundleCycles.localizedEquationCokernelEquiv P.primeCompl b).length_eq] at h
  change Module.length (Localization P.primeCompl)
    ((Localization P.primeCompl) ⧸ Ideal.span {algebraMap R (Localization P.primeCompl) b}) ≠ ⊤
  rw [h]
  exact ENat.natCast_ne_top _

variable [IsDomain R] [IsLocalRing R]

/-- The two orders of proper local divisor intersection have equal actual coefficients. -/
theorem surfaceIntersectionNumber_comm (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R) :
    SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber a b = SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber b a := by
  have hba : (Ideal.span {b, a}).radical = IsLocalRing.maximalIdeal R :=
    (congrArg Ideal.radical (Ideal.span_pair_comm (x := b) (y := a))).trans hab
  exact (SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber_eq_localIntersectionLength a b hb hdim hab).trans
    ((LocalIntersectionLength.BundleCycles.localIntersectionLength_comm a b ha hb _).trans
      (SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber_eq_localIntersectionLength b a ha hdim hba).symm)

end

section

/-!
# LineBundleCycles: rational order as a difference of actual quotient lengths

For a one-dimensional Noetherian domain, the existing fraction-field
order of a/b equals the length of R/aR minus the length of R/bR.
This supplies the rational-function form of the local intersection
formula, with the same integer convention as Scheme.ord.
-/

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

def fractionFieldOrder (g : K) : ℤ :=
  Multiplicative.toAdd ((Ring.ordFrac R g).unzeroD 1)

theorem fractionFieldOrder_div (a c : R) (ha : a ≠ 0) (hc : c ≠ 0) :
    fractionFieldOrder R (algebraMap R K a / algebraMap R K c) =
      ((Ring.ord R a).toNat : ℤ) - (Ring.ord R c).toNat := by
  have ha' := mem_nonZeroDivisors_iff_ne_zero.mpr ha
  have hc' := mem_nonZeroDivisors_iff_ne_zero.mpr hc
  have hA := Ring.ordMonoidWithZeroHom_eq_coe R ha'
    (ENat.natCast_toNat (Ring.ord_ne_top ha')).symm
  have hC := Ring.ordMonoidWithZeroHom_eq_coe R hc'
    (ENat.natCast_toNat (Ring.ord_ne_top hc')).symm
  unfold fractionFieldOrder
  rw [map_div₀, Ring.ordFrac_eq_ord R ha, Ring.ordFrac_eq_ord R hc, hA, hC, ← WithZero.coe_div]
  rfl

end

section

/-!
# LineBundleCycles: quotient lengths are orders on the actual prime support

The double quotient identification respects the R-algebra structure.
Restriction of scalars along R → R/P preserves module length, so the
prime-support quotient length is the ring order on R/P itself. A prime
containing a nonzero equation in a local surface has quotient dimension
at most one, as required for its rational order.
-/

variable {R : Type*} [CommRing R]

theorem primeIntersectionQuotientLength_eq_ord (a : R) (P : Ideal R) :
    PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength a P = (Ring.ord (R ⧸ P) (Ideal.Quotient.mk P a)).toNat := by
  let J := (Ideal.span {a}).map (Ideal.Quotient.mkₐ R P)
  have hJ : J = Ideal.span {Ideal.Quotient.mk P a} := by
    dsimp only [J]
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  have he := (DoubleQuot.quotQuotEquivQuotSupₐ R P (Ideal.span {a})).toLinearEquiv.length_eq
  have hl := Module.length_eq_of_surjective (R := R ⧸ P) (S := R)
    (M := (R ⧸ P) ⧸ J) Ideal.Quotient.mk_surjective
  unfold PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength Ring.ord
  rw [← he, hl, hJ]

theorem surfacePrimeSupport_krullDimLE [IsDomain R] (b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (P : Ideal R) (hbP : b ∈ P) : Ring.KrullDimLE 1 (R ⧸ P) := by
  have h := (ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    (mem_nonZeroDivisors_iff_ne_zero.mpr hb) (Ideal.Quotient.eq_zero_iff_mem.mpr hbP)).trans hdim.le
  apply Ring.krullDimLE_iff.mpr
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  exact h

end

section

/-!
# LineBundleCycles: the actual rational function on a prime surface section

Reduce a and c in R/P and take their ratio in that quotient domain's
fraction field. Its order is computed by the proved quotient-length
formula whenever neither equation vanishes identically on the support.
All dimension and Noetherian instances come from the actual surface ring.
-/

variable {R : Type*} [CommRing R]

def primeSupportRationalFunction (a c : R) (P : Ideal R) [P.IsPrime] : FractionRing (R ⧸ P) :=
  algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P a) /
    algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P c)

variable [IsNoetherianRing R] [IsDomain R]

def surfacePrimeRationalOrder (a c b : R) (hb : b ≠ 0) (hdim : ringKrullDim R = 2)
    (P : Ideal R) (hP : P ∈ (Ideal.span {b}).minimalPrimes) : ℤ :=
  letI : P.IsPrime := hP.isPrime
  letI : IsNoetherianRing (R ⧸ P) :=
    isNoetherianRing_of_surjective R (R ⧸ P) (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  letI : Ring.KrullDimLE 1 (R ⧸ P) :=
    surfacePrimeSupport_krullDimLE b hb hdim P (hP.le (Ideal.subset_span (Set.mem_singleton b)))
  fractionFieldOrder (R ⧸ P) (primeSupportRationalFunction a c P)

theorem surfacePrimeRationalOrder_eq_difference (a c b : R) (hb : b ≠ 0) (hdim : ringKrullDim R = 2)
    (P : Ideal R) (hP : P ∈ (Ideal.span {b}).minimalPrimes) (ha : a ∉ P) (hc : c ∉ P) :
    surfacePrimeRationalOrder a c b hb hdim P hP =
      PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength a P - PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength c P := by
  let : P.IsPrime := hP.isPrime
  let : IsNoetherianRing (R ⧸ P) :=
    isNoetherianRing_of_surjective R (R ⧸ P) (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : Ring.KrullDimLE 1 (R ⧸ P) :=
    surfacePrimeSupport_krullDimLE b hb hdim P (hP.le (Ideal.subset_span (Set.mem_singleton b)))
  have ha' : Ideal.Quotient.mk P a ≠ 0 := fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hc' : Ideal.Quotient.mk P c ≠ 0 := fun h => hc (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact (fractionFieldOrder_div (K := FractionRing (R ⧸ P)) (R ⧸ P) _ _ ha' hc').trans
    (congrArg₂ (· - ·) (primeIntersectionQuotientLength_eq_ord a P).symm
      (primeIntersectionQuotientLength_eq_ord c P).symm)

end

section

/-!
# LineBundleCycles: rational local surface intersections with proper representatives

On each prime component of b = 0, take the actual rational function
a/c in its fraction field and its existing ring order. The weighted sum
equals I(a,b)-I(c,b), and symmetry also identifies it with I(b,a)-I(b,c).
The only restrictions are that the two numerator/denominator intersections
are proper; no equality of intersection numbers is assumed.
-/

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]

def surfaceRationalIntersectionSummand (a c b : R) (hb : b ≠ 0) (hdim : ringKrullDim R = 2)
    (P : Ideal R) : ℤ := by
  classical
  exact if hP : P ∈ (Ideal.span {b}).minimalPrimes then
    (LocalizedEquationLength.BundleCycles.primeEquationMultiplicity b P hP.isPrime : ℤ) * surfacePrimeRationalOrder a c b hb hdim P hP else 0

def surfaceRationalIntersectionNumber (a c b : R) (hb : b ≠ 0) (hdim : ringKrullDim R = 2) : ℤ :=
  ∑ P ∈ (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).toFinset,
    surfaceRationalIntersectionSummand a c b hb hdim P

variable [IsLocalRing R]
variable (a c b : R) (hb : b ≠ 0) (hdim : ringKrullDim R = 2)
variable (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R)
variable (hcb : (Ideal.span {c, b}).radical = IsLocalRing.maximalIdeal R)

include hab hcb

theorem surfaceRationalIntersectionSummand_eq_sub (P : Ideal R) :
    surfaceRationalIntersectionSummand a c b hb hdim P =
      SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionSummand a b P - SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionSummand c b P := by
  classical
  by_cases hP : P ∈ (Ideal.span {b}).minimalPrimes
  · rw [surfaceRationalIntersectionSummand, dite_eq_left hP,
      SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionSummand, dite_eq_left hP, SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionSummand, dite_eq_left hP,
      surfacePrimeRationalOrder_eq_difference a c b hb hdim P hP
        (SurfaceParameters.BundleCycles.surfaceParameter_not_mem_minimal a b hdim hab P hP)
        (SurfaceParameters.BundleCycles.surfaceParameter_not_mem_minimal c b hdim hcb P hP), mul_sub]
  · rw [surfaceRationalIntersectionSummand, dite_eq_right hP,
      SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionSummand, dite_eq_right hP, SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionSummand, dite_eq_right hP, sub_zero]

theorem surfaceRationalIntersectionNumber_eq_sub :
    surfaceRationalIntersectionNumber a c b hb hdim =
      SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber a b - SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber c b := by
  unfold surfaceRationalIntersectionNumber SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun P _ => surfaceRationalIntersectionSummand_eq_sub a c b hb hdim hab hcb P)

/-- Local rational order on the section equals the difference of the two opposite intersections. -/
theorem surfaceRationalIntersectionNumber_eq_opposite_sub (ha : a ≠ 0) (hc : c ≠ 0) :
    surfaceRationalIntersectionNumber a c b hb hdim =
      SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber b a - SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber b c :=
  (surfaceRationalIntersectionNumber_eq_sub a c b hb hdim hab hcb).trans
    (congrArg₂ (· - ·) (surfaceIntersectionNumber_comm a b ha hb hdim hab)
      (surfaceIntersectionNumber_comm c b hc hb hdim hcb))

end

/-!
# LineBundleCycles: the regular local surface formula is the rational formula with denominator one

A unit denominator contributes zero quotient length. The actual rational
order on every prime support is therefore the ordinary intersection
length, without imposing a spurious proper-intersection condition on 1.
-/

variable {R : Type*} [CommRing R]

theorem primeIntersectionQuotientLength_one (P : Ideal R) :
    PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength (1 : R) P = 0 := by
  rw [primeIntersectionQuotientLength_eq_ord, map_one, Ring.ord_one]
  rfl

variable [IsNoetherianRing R] [IsDomain R] [IsLocalRing R]

theorem surfaceRationalIntersectionSummand_one_denominator (a b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R) (P : Ideal R) :
    surfaceRationalIntersectionSummand a 1 b hb hdim P = SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionSummand a b P := by
  classical
  by_cases hP : P ∈ (Ideal.span {b}).minimalPrimes
  · rw [surfaceRationalIntersectionSummand, dite_eq_left hP,
      surfacePrimeRationalOrder_eq_difference a 1 b hb hdim P hP
        (SurfaceParameters.BundleCycles.surfaceParameter_not_mem_minimal a b hdim hab P hP)
        (fun h => hP.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem P h isUnit_one)),
      primeIntersectionQuotientLength_one, sub_zero, SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionSummand, dite_eq_left hP]
  · rw [surfaceRationalIntersectionSummand, dite_eq_right hP, SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionSummand, dite_eq_right hP]

theorem surfaceRationalIntersectionNumber_one_denominator (a b : R) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R) :
    surfaceRationalIntersectionNumber a 1 b hb hdim = SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber a b := by
  unfold surfaceRationalIntersectionNumber SurfaceIntersectionFormula.BundleCycles.surfaceIntersectionNumber
  exact Finset.sum_congr rfl (fun P _ => surfaceRationalIntersectionSummand_one_denominator a b hb hdim hab P)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceRationalOrderIntersection.BundleCycles
