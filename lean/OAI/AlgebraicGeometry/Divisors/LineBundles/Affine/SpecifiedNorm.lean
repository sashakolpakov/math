import OAI.AlgebraicGeometry.Divisors.LineBundles.FractionNormTransport

/-! # Specified Norm -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecifiedNorm.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite affine norm-divisor pushforward in actual field coordinates
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

local instance specifiedNorm_affineAlgebra (S : Type) [CommRing S] [IsDomain S] :
    Algebra S (Spec (CommRingCat.of S)).functionField :=
  (StructureSheaf.toStalk S (genericPoint (Spec (CommRingCat.of S)))).hom.toAlgebra

theorem normalAffineFieldIso_specified (S : Type) [CommRing S] [IsDedekindDomain S]
    (L : Type) [Field L] [Algebra S L] [IsFractionRing S L] (g : FractionRing S) :
    (FractionField.BundleCycles.AffineFractionField.fieldIso S L).hom (Normal.AffineOrder.BundleCycles.normalAffineFieldIso S g) =
      FractionRing.algEquiv S L g := by
  let : IsFractionRing S (Spec (CommRingCat.of S)).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of S)
  let e : FractionRing S ≃ₐ[S] L := (Normal.AffineOrder.BundleCycles.normalAffineFieldIso S).trans
    (IsLocalization.algEquiv (nonZeroDivisors S) (Spec (CommRingCat.of S)).functionField L)
  have h : e.toAlgHom = (FractionRing.algEquiv S L).toAlgHom :=
    (IsLocalization.algHom_subsingleton (nonZeroDivisors S)).elim _ _
  exact congrArg (fun t : FractionRing S →ₐ[S] L => t g) h

variable (R S : Type) [CommRing R] [CommRing S] [IsDomain R]
    [IsDiscreteValuationRing R] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [PerfectField (FractionRing R)]
    (K L : Type) [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra R L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]

theorem affineSpecifiedNormPrincipalDivisor_pushforward
    (g : (Spec (CommRingCat.of S)).functionField) (hg : g ≠ 0) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of S)) g) =
        Finsupp.single (IsLocalRing.closedPoint R : Spec (CommRingCat.of R))
          ((WithZero.log (Ring.ordFrac R
            (Algebra.norm K ((FractionField.BundleCycles.AffineFractionField.fieldIso S L).hom g))) : ℤ) : ℚ) := by
  obtain ⟨a, rfl⟩ := (Normal.AffineOrder.BundleCycles.normalAffineFieldIso S).surjective g
  have ha : a ≠ 0 := fun h => hg (by rw [h, map_zero])
  rw [NormDivisor.BundleCycles.affineNormPrincipalDivisor_pushforward R S a ha, normalAffineFieldIso_specified]
  exact congrArg (fun t : WithZero (Multiplicative ℤ) =>
    Finsupp.single (IsLocalRing.closedPoint R : Spec (CommRingCat.of R))
      ((WithZero.log t : ℤ) : ℚ)) (FractionNormTransport.BundleCycles.fractionNorm_order R S K L a)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecifiedNorm.BundleCycles
