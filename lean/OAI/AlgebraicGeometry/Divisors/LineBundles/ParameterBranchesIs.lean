import OAI.AlgebraicGeometry.Divisors.LineBundles.CurveParameterImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Place
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecifiedNorm
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! # Parameter Branches Is -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Divisors.LineBundles.ParameterBranchesIs.BundleCycles.ParameterBranches

/-! The normalized branches over a rational parameter's zero place have
total order equal to the degree of the parameter's function-field extension.
The cycle statement uses all branches with their actual residue degrees. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.CurveParameterImage.BundleCycles.CurveParameter OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace

variable (k L : Type) [Field k] [Field L] [Algebra k L]
  (g : L) (hg : Transcendental k g)

abbrev localAlgebra : Algebra (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L :=
  letI := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
  letI := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
  ((algebraMap (FractionRing (Polynomial k)) L).comp
    (algebraMap (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)))).toAlgebra

theorem localTower :
    letI := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
    letI := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
    letI := localAlgebra k L g hg
    IsScalarTower (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)) L := by
  let := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
  let := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
  let := localAlgebra k L g hg
  exact IsScalarTower.of_algebraMap_eq' rfl

theorem norm_order :
    letI := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
    letI := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
    WithZero.log (Ring.ordFrac (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (Algebra.norm (FractionRing (Polynomial k)) g)) =
      Module.finrank (FractionRing (Polynomial k)) L := by
  let := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
  let := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
  have h := CurveParameterImage.BundleCycles.CurveParameter.parameter_image k L g hg
  change algebraMap (FractionRing (Polynomial k)) L (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k) = g at h
  have hn : Algebra.norm (FractionRing (Polynomial k)) g =
      LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k ^ Module.finrank (FractionRing (Polynomial k)) L :=
    (congrArg (Algebra.norm (FractionRing (Polynomial k))) h).symm.trans
      (Algebra.norm_algebraMap (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.parameter k))
  rw [hn, LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.order_parameter_pow]

variable [CharZero k] [Algebra.EssFiniteType k L] (hdim : Algebra.trdeg k L = 1)

include hdim in
theorem closure_finite :
    letI := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
    letI := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
    letI := localAlgebra k L g hg
    Module.Finite (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L) := by
  let := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
  let := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
  let := localAlgebra k L g hg
  let := localTower k L g hg
  let := CurveParameterImage.BundleCycles.CurveParameter.finite_parameter_extension k L hdim g hg
  exact IsIntegralClosure.finite (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)) L
    (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L)

include hdim in
theorem closure_dedekind :
    letI := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
    letI := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
    letI := localAlgebra k L g hg
    IsDedekindDomain (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L) := by
  let := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
  let := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
  let := localAlgebra k L g hg
  let := localTower k L g hg
  let := CurveParameterImage.BundleCycles.CurveParameter.finite_parameter_extension k L hdim g hg
  exact integralClosure.isDedekindDomain (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)) L

/-- Every branch over the zero place is included in this native finite
cycle pushforward, whose coefficient is the extension degree. -/
theorem parameter_divisor_pushforward :
    letI := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
    letI := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
    letI := localAlgebra k L g hg
    letI := localTower k L g hg
    letI := CurveParameterImage.BundleCycles.CurveParameter.finite_parameter_extension k L hdim g hg
    letI := closure_dedekind k L g hg hdim
    letI : IsFractionRing (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L) L :=
      integralClosure.isFractionRing_of_finite_extension (FractionRing (Polynomial k)) L
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom
      (algebraMap (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L))))
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor
        (Spec (.of (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L)))
        ((Affine.FractionField.BundleCycles.AffineFractionField.fieldIso (integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L) L).inv g)) =
      Finsupp.single (IsLocalRing.closedPoint (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k))
        (Module.finrank (FractionRing (Polynomial k)) L : ℚ) := by
  let := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
  let := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
  let := localAlgebra k L g hg
  let := localTower k L g hg
  let := CurveParameterImage.BundleCycles.CurveParameter.finite_parameter_extension k L hdim g hg
  let := closure_dedekind k L g hg hdim
  let := closure_finite k L g hg hdim
  let D := integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L
  let : IsFractionRing D L :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing (Polynomial k)) L
  let : Module.IsTorsionFree (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L :=
    .trans_faithfulSMul (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)) L
  let : Module.IsTorsionFree (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) D := IsIntegralClosure.isTorsionFree (A := D) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L
  let : CharZero (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) := (algebraMap (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k))).charZero
  have hg0 : g ≠ 0 := fun h => hg (h ▸ isAlgebraic_zero)
  have hginv : (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso D L).inv g ≠ 0 :=
    (map_ne_zero_iff _ (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso D L).symm.commRingCatIsoToRingEquiv.injective).mpr hg0
  have h := Affine.SpecifiedNorm.BundleCycles.affineSpecifiedNormPrincipalDivisor_pushforward (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) D
    (FractionRing (Polynomial k)) L ((Affine.FractionField.BundleCycles.AffineFractionField.fieldIso D L).inv g) hginv
  have he : (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso D L).hom ((Affine.FractionField.BundleCycles.AffineFractionField.fieldIso D L).inv g) = g :=
    (Affine.FractionField.BundleCycles.AffineFractionField.fieldIso D L).commRingCatIsoToRingEquiv.apply_symm_apply g
  have hv := (congrArg (fun x : L => WithZero.log
    (Ring.ordFrac (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (Algebra.norm (FractionRing (Polynomial k)) x))) he).trans
      (norm_order k L g hg)
  refine h.trans (congrArg (Finsupp.single (IsLocalRing.closedPoint (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) : Spec (.of (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k)))) ?_)
  exact_mod_cast hv

end AlgebraicGeometry.Divisors.LineBundles.ParameterBranchesIs.BundleCycles.ParameterBranches

namespace AlgebraicGeometry.Divisors.LineBundles.ParameterBranchesIs.BundleCycles.ParameterLocalMap

/-! A function vanishing in a local ring defines an actual map from
the parameter's zero local ring, with its prescribed fraction-field map. -/

open IsLocalRing

open OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace OAI.AlgebraicGeometry.Divisors.LineBundles.CurveParameterImage.BundleCycles.CurveParameter OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterBranchesIs.BundleCycles.ParameterBranches

variable (k B : Type) [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]
  (b : B) (hb : b ∈ maximalIdeal B)

include hb

theorem aeval_isUnit (p : Polynomial k) (hp : p ∈ (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.zeroIdeal k).primeCompl) :
    IsUnit (Polynomial.aeval b p) := by
  have hc : p.coeff 0 ≠ 0 := by
    intro h
    exact hp (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_iff.mpr h))
  apply (residue_ne_zero_iff_isUnit _).mp
  have he := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k B (ResidueField B)) b p
  change Polynomial.aeval (algebraMap B (ResidueField B) b) p =
    algebraMap B (ResidueField B) (Polynomial.aeval b p) at he
  have hz : algebraMap B (ResidueField B) b = 0 := (residue_eq_zero_iff b).mpr hb
  rw [hz, ← Polynomial.coeff_zero_eq_aeval_zero'] at he
  change algebraMap B (ResidueField B) (Polynomial.aeval b p) ≠ 0
  rw [← he]
  exact (map_ne_zero_iff _ (algebraMap k (ResidueField B)).injective).mpr hc

def localMap : LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k →+* B :=
  IsLocalization.lift (M := (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.zeroIdeal k).primeCompl)
    (g := (Polynomial.aeval b).toRingHom)
    (fun p => aeval_isUnit k B b hb p p.property)

theorem localMap_algebraMap (p : Polynomial k) :
    localMap k B b hb (algebraMap (Polynomial k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) p) = Polynomial.aeval b p :=
  IsLocalization.lift_eq _ p

variable (L : Type) [Field L] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  (g : L) (hg : Transcendental k g) (hbg : algebraMap B L b = g)

include hbg

theorem localMap_field :
    letI := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
    letI := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
    letI := ParameterBranches.localAlgebra k L g hg
    (algebraMap B L).comp (localMap k B b hb) = algebraMap (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L := by
  let := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra k L g
  let := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra k L g hg
  let := ParameterBranches.localAlgebra k L g hg
  let := ParameterBranches.localTower k L g hg
  let : FaithfulSMul (Polynomial k) L :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial k) L).mpr (CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra_injective k L g hg)
  let : IsScalarTower (Polynomial k) (FractionRing (Polynomial k)) L :=
    FractionRing.isScalarTower_liftAlgebra (Polynomial k) L
  apply IsLocalization.ringHom_ext (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.zeroIdeal k).primeCompl
  apply RingHom.ext
  intro p
  change algebraMap B L (localMap k B b hb (algebraMap (Polynomial k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) p)) =
    algebraMap (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) L (algebraMap (Polynomial k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) p)
  rw [localMap_algebraMap, IsScalarTower.algebraMap_apply (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)) L,
    ← IsScalarTower.algebraMap_apply (Polynomial k) (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing k) (FractionRing (Polynomial k)),
    ← IsScalarTower.algebraMap_apply]
  exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k B L) b p).symm.trans
    (congrArg (fun x : L => Polynomial.aeval x p) hbg)

end AlgebraicGeometry.Divisors.LineBundles.ParameterBranchesIs.BundleCycles.ParameterLocalMap

end

end OAI
