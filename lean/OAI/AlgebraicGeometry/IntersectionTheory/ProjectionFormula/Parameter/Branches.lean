import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveParameter
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.NormFields
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! # Branches -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Branches

noncomputable section

/-! The normalized branches over a rational parameter's zero place have
total order equal to the degree of the parameter's function-field extension.
The cycle statement uses all branches with their actual residue degrees. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveParameter OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place

variable (k L : Type) [Field k] [Field L] [Algebra k L]
  (g : L) (hg : Transcendental k g)

abbrev localAlgebra : Algebra (ProjectionFormula.Polynomial.Place.localRing k) L :=
  letI := CurveParameter.polynomialAlgebra k L g
  letI := CurveParameter.fractionAlgebra k L g hg
  ((algebraMap (FractionRing (Polynomial k)) L).comp
    (algebraMap (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)))).toAlgebra

theorem localTower :
    letI := CurveParameter.polynomialAlgebra k L g
    letI := CurveParameter.fractionAlgebra k L g hg
    letI := localAlgebra k L g hg
    IsScalarTower (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)) L := by
  let := CurveParameter.polynomialAlgebra k L g
  let := CurveParameter.fractionAlgebra k L g hg
  let := localAlgebra k L g hg
  exact IsScalarTower.of_algebraMap_eq' rfl

theorem norm_order :
    letI := CurveParameter.polynomialAlgebra k L g
    letI := CurveParameter.fractionAlgebra k L g hg
    WithZero.log (Ring.ordFrac (ProjectionFormula.Polynomial.Place.localRing k) (Algebra.norm (FractionRing (Polynomial k)) g)) =
      Module.finrank (FractionRing (Polynomial k)) L := by
  let := CurveParameter.polynomialAlgebra k L g
  let := CurveParameter.fractionAlgebra k L g hg
  have h := CurveParameter.parameter_image k L g hg
  change algebraMap (FractionRing (Polynomial k)) L (ProjectionFormula.Polynomial.Place.parameter k) = g at h
  have hn : Algebra.norm (FractionRing (Polynomial k)) g =
      ProjectionFormula.Polynomial.Place.parameter k ^ Module.finrank (FractionRing (Polynomial k)) L :=
    (congrArg (Algebra.norm (FractionRing (Polynomial k))) h).symm.trans
      (Algebra.norm_algebraMap (ProjectionFormula.Polynomial.Place.parameter k))
  rw [hn, ProjectionFormula.Polynomial.Place.order_parameter_pow]

variable [CharZero k] [Algebra.EssFiniteType k L] (hdim : Algebra.trdeg k L = 1)

include hdim in
theorem closure_finite :
    letI := CurveParameter.polynomialAlgebra k L g
    letI := CurveParameter.fractionAlgebra k L g hg
    letI := localAlgebra k L g hg
    Module.Finite (ProjectionFormula.Polynomial.Place.localRing k) (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L) := by
  let := CurveParameter.polynomialAlgebra k L g
  let := CurveParameter.fractionAlgebra k L g hg
  let := localAlgebra k L g hg
  let := localTower k L g hg
  let := CurveParameter.finite_parameter_extension k L hdim g hg
  exact IsIntegralClosure.finite (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)) L
    (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L)

include hdim in
theorem closure_dedekind :
    letI := CurveParameter.polynomialAlgebra k L g
    letI := CurveParameter.fractionAlgebra k L g hg
    letI := localAlgebra k L g hg
    IsDedekindDomain (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L) := by
  let := CurveParameter.polynomialAlgebra k L g
  let := CurveParameter.fractionAlgebra k L g hg
  let := localAlgebra k L g hg
  let := localTower k L g hg
  let := CurveParameter.finite_parameter_extension k L hdim g hg
  exact integralClosure.isDedekindDomain (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)) L

/-- Every branch over the zero place is included in this native finite
cycle pushforward, whose coefficient is the extension degree. -/
theorem parameter_divisor_pushforward :
    letI := CurveParameter.polynomialAlgebra k L g
    letI := CurveParameter.fractionAlgebra k L g hg
    letI := localAlgebra k L g hg
    letI := localTower k L g hg
    letI := CurveParameter.finite_parameter_extension k L hdim g hg
    letI := closure_dedekind k L g hg hdim
    letI : IsFractionRing (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L) L :=
      integralClosure.isFractionRing_of_finite_extension (FractionRing (Polynomial k)) L
    CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom
      (algebraMap (ProjectionFormula.Polynomial.Place.localRing k) (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L))))
      (Affine.DivisorNorm.rationalPrincipalDivisor
        (Spec (.of (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L)))
        ((Affine.FractionField.fieldIso (integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L) L).inv g)) =
      Finsupp.single (IsLocalRing.closedPoint (ProjectionFormula.Polynomial.Place.localRing k))
        (Module.finrank (FractionRing (Polynomial k)) L : ℚ) := by
  let := CurveParameter.polynomialAlgebra k L g
  let := CurveParameter.fractionAlgebra k L g hg
  let := localAlgebra k L g hg
  let := localTower k L g hg
  let := CurveParameter.finite_parameter_extension k L hdim g hg
  let := closure_dedekind k L g hg hdim
  let := closure_finite k L g hg hdim
  let D := integralClosure (ProjectionFormula.Polynomial.Place.localRing k) L
  let : IsFractionRing D L :=
    integralClosure.isFractionRing_of_finite_extension (FractionRing (Polynomial k)) L
  let : Module.IsTorsionFree (ProjectionFormula.Polynomial.Place.localRing k) L :=
    .trans_faithfulSMul (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k)) L
  let : Module.IsTorsionFree (ProjectionFormula.Polynomial.Place.localRing k) D := IsIntegralClosure.isTorsionFree (A := D) (ProjectionFormula.Polynomial.Place.localRing k) L
  let : CharZero (ProjectionFormula.Polynomial.Place.localRing k) := (algebraMap (ProjectionFormula.Polynomial.Place.localRing k) (FractionRing (Polynomial k))).charZero
  have hg0 : g ≠ 0 := fun h => hg (h ▸ isAlgebraic_zero)
  have hginv : (Affine.FractionField.fieldIso D L).inv g ≠ 0 :=
    (map_ne_zero_iff _ (Affine.FractionField.fieldIso D L).symm.commRingCatIsoToRingEquiv.injective).mpr hg0
  have h := Affine.NormFields.principalDivisor_pushforward (ProjectionFormula.Polynomial.Place.localRing k) D
    (FractionRing (Polynomial k)) L ((Affine.FractionField.fieldIso D L).inv g) hginv
  have he : (Affine.FractionField.fieldIso D L).hom ((Affine.FractionField.fieldIso D L).inv g) = g :=
    (Affine.FractionField.fieldIso D L).commRingCatIsoToRingEquiv.apply_symm_apply g
  have hv := (congrArg (fun x : L => WithZero.log
    (Ring.ordFrac (ProjectionFormula.Polynomial.Place.localRing k) (Algebra.norm (FractionRing (Polynomial k)) x))) he).trans
      (norm_order k L g hg)
  refine h.trans (congrArg (Finsupp.single (IsLocalRing.closedPoint (ProjectionFormula.Polynomial.Place.localRing k) : Spec (.of (ProjectionFormula.Polynomial.Place.localRing k)))) ?_)
  exact_mod_cast hv

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Branches
