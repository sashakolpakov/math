import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrimeSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceRationalOrderIntersection

/-! # Local Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.LocalDivisor.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: the native closed-point order on an arbitrary local integral curve

The stalk at the closed point of Spec R is canonically R. Together with
the actual generic-field map, this identifies Scheme.ord with the
existing rational ring order, including for singular local domains.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable (R : Type) [CommRing R] [IsDomain R]

local instance affineLocalOrder_fieldAlgebra : Algebra R (Spec (CommRingCat.of R)).functionField :=
  (StructureSheaf.toStalk R (genericPoint (Spec (CommRingCat.of R)))).hom.toAlgebra

local instance affineLocalOrder_isFractionRing : IsFractionRing R (Spec (CommRingCat.of R)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of R)

def affineGenericFieldIso : FractionRing R ≃ₐ[R] (Spec (CommRingCat.of R)).functionField :=
  FractionRing.algEquiv R (Spec (CommRingCat.of R)).functionField

variable [IsLocalRing R]

def affineLocalClosedPoint : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R

def affineClosedStalkIso : R ≃+*
    (Spec (CommRingCat.of R)).presheaf.stalk (affineLocalClosedPoint R) :=
  (stalkClosedPointIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv

omit [IsDomain R] in
theorem affineLocalClosedPoint_coheight (hdim : ringKrullDim R = 1) :
    coheight (affineLocalClosedPoint R) = 1 := by
  have he := (ringKrullDim_eq_of_ringEquiv (affineClosedStalkIso R)).symm
  rw [ringKrullDim_stalk_eq_coheight] at he
  exact WithBot.coe_inj.mp (he.trans hdim)

theorem affineClosedStalkIso_generic (a : R) :
    affineGenericFieldIso R (algebraMap R (FractionRing R) a) =
      algebraMap ((Spec (CommRingCat.of R)).presheaf.stalk (affineLocalClosedPoint R))
        (Spec (CommRingCat.of R)).functionField (affineClosedStalkIso R a) := by
  have hi : affineClosedStalkIso R a = StructureSheaf.toStalk R (affineLocalClosedPoint R) a :=
    congrArg (fun j : CommRingCat.of R ⟶
      (Spec (CommRingCat.of R)).presheaf.stalk (affineLocalClosedPoint R) => j a)
      (stalkClosedPointIso_inv (CommRingCat.of R))
  rw [AlgEquiv.commutes, hi]
  exact (congrArg (fun j : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).functionField => j a)
    (StructureSheaf.toStalk_stalkSpecializes
      ((genericPoint_spec (Spec (CommRingCat.of R))).specializes trivial))).symm

variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

theorem affineLocalOrder_eq_ringOrder
    (hx : coheight (affineLocalClosedPoint R) = 1)
    (g : FractionRing R) :
    (Spec (CommRingCat.of R)).ord (affineGenericFieldIso R g) (affineLocalClosedPoint R) =
      SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R g := by
  let : Ring.KrullDimLE 1
      ((Spec (CommRingCat.of R)).presheaf.stalk (affineLocalClosedPoint R)) :=
    krullDimLE_of_coheight_le hx.le
  rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hx]
  exact congrArg (fun z : WithZero (Multiplicative ℤ) => Multiplicative.toAdd (z.unzeroD 1))
    (RationalDivisorRestriction.BundleCycles.ringOrderFrac_equiv (affineClosedStalkIso R) (affineGenericFieldIso R).toRingEquiv
      (affineClosedStalkIso_generic R) g)

end

section

/-!
# LineBundleCycles: the complete divisor on an actual one-dimensional local spectrum

The only possible divisor point is the closed point. Its coefficient
is the existing rational ring order, with no normality assumption.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order
open scoped Classical

variable (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

local instance affineLocalDivisor_fieldAlgebra : Algebra R (Spec (CommRingCat.of R)).functionField :=
  (StructureSheaf.toStalk R (genericPoint (Spec (CommRingCat.of R)))).hom.toAlgebra

local instance affineLocalDivisor_isFractionRing : IsFractionRing R (Spec (CommRingCat.of R)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of R)

theorem affineLocal_principalDivisor (hdim : ringKrullDim R = 1) (g : FractionRing R) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of R)) (affineGenericFieldIso R g) =
      Finsupp.single (affineLocalClosedPoint R) (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder R g : ℚ) := by
  ext x
  rw [RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply]
  by_cases hx : x.asIdeal = ⊥
  · have hc : coheight x ≠ 1 := by
      rw [← idealHeight_eq_coheight, hx, Ideal.height_bot]
      decide
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hc, Int.cast_zero]
    symm
    apply Finsupp.single_eq_of_ne
    intro he
    have hhc := affineLocalClosedPoint_coheight R hdim
    exact hc ((congrArg coheight he).trans hhc)
  · have he : x = affineLocalClosedPoint R := by
      apply PrimeSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal_of_ne_bot hx)
    rw [he, Finsupp.single_eq_same,
      affineLocalOrder_eq_ringOrder R (affineLocalClosedPoint_coheight R hdim)]

end

/-!
# LineBundleCycles: a prime local curve's divisor as an actual ambient geometric cycle

The quotient spectrum is its reduced image support, and its closed point
maps to the ambient closed point. The complete transported principal
divisor therefore has its actual rational ring order as sole coefficient.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

local instance affinePrimeLocal_fieldAlgebra (S : Type) [CommRing S] [IsDomain S] : Algebra S (Spec (.of S)).functionField :=
  (StructureSheaf.toStalk S (genericPoint (Spec (.of S)))).hom.toAlgebra

local instance affinePrimeLocal_isFractionRing (S : Type) [CommRing S] [IsDomain S] : IsFractionRing S (Spec (.of S)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of S)

variable (R : Type) [CommRing R] (P : Ideal R) [P.IsPrime]

def affinePrimeLocalFunction (g : FractionRing (R ⧸ P)) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (CycleClass.Geometric.StratumClosure.integralImageClosure (PrimeSupport.BundleCycles.affinePrimeQuotientMap R P))).functionField :=
  Integral.ClosedImage.BundleCycles.integralClosedImageFunction (PrimeSupport.BundleCycles.affinePrimeQuotientMap R P) (affineGenericFieldIso (R ⧸ P) g)

variable [IsLocalRing R]

local instance affinePrimeLocal_quotientLocalRing : IsLocalRing (R ⧸ P) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective

theorem affinePrimeQuotientMap_closedPoint :
    PrimeSupport.BundleCycles.affinePrimeQuotientMap R P (affineLocalClosedPoint (R ⧸ P)) = affineLocalClosedPoint R := by
  let : IsLocalHom (Ideal.Quotient.mk P) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  exact Spec_closedPoint (f := CommRingCat.ofHom (Ideal.Quotient.mk P))

variable [IsNoetherianRing R]

theorem affinePrimeLocal_principalDivisor (hdim : ringKrullDim (R ⧸ P) = 1)
    (g : FractionRing (R ⧸ P)) :
    letI : Ring.KrullDimLE 1 (R ⧸ P) := Ring.krullDimLE_iff.mpr hdim.le
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (CycleClass.Geometric.StratumClosure.integralImageClosure (PrimeSupport.BundleCycles.affinePrimeQuotientMap R P))
      (affinePrimeLocalFunction R P g) =
        Finsupp.single (affineLocalClosedPoint R) (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (R ⧸ P) g : ℚ) := by
  let : Ring.KrullDimLE 1 (R ⧸ P) := Ring.krullDimLE_iff.mpr hdim.le
  change Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (CycleClass.Geometric.StratumClosure.integralImageClosure (PrimeSupport.BundleCycles.affinePrimeQuotientMap R P))
    (Integral.ClosedImage.BundleCycles.integralClosedImageFunction (PrimeSupport.BundleCycles.affinePrimeQuotientMap R P) (affineGenericFieldIso (R ⧸ P) g)) = _
  rw [← PrimeSupport.BundleCycles.affinePrimeSupport_principalDivisor, affineLocal_principalDivisor (R ⧸ P) hdim,
    Finsupp.mapDomain_single, affinePrimeQuotientMap_closedPoint]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.LocalDivisor.BundleCycles
