import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.AffineOrder
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ResidueDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

/-! # Branch Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.BranchPushforward.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: actual pushforward of a finite normal affine divisor

Every branch over a local base maps to its closed point. The native
scheme residue degrees give precisely the algebraic inertia weights.
The resulting formula includes every branch and every pole.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory IsDedekindDomain _root_.Order
open scoped Classical BigOperators

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable (S : Type) [CommRing S] [IsDedekindDomain S]

omit [IsDedekindDomain S] in
theorem normalBranchPoint_injective : Function.Injective (AffineOrder.BundleCycles.normalBranchPoint S) := by
  intro P Q h
  exact HeightOneSpectrum.ext (congrArg PrimeSpectrum.asIdeal h)

theorem normalPrincipalPointDivisor_eq_sum [Fintype (HeightOneSpectrum S)]
    (g : (Spec (CommRingCat.of S)).functionField) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of S)) g =
      ∑ P : HeightOneSpectrum S, Finsupp.single (AffineOrder.BundleCycles.normalBranchPoint S P)
        ((Spec (CommRingCat.of S)).ord g (AffineOrder.BundleCycles.normalBranchPoint S P) : ℚ) := by
  ext x
  change ((Spec (CommRingCat.of S)).ord g x : ℚ) = _
  rw [Finsupp.finsetSum_apply]
  by_cases hx : x.asIdeal = ⊥
  · have hc : coheight x ≠ 1 := by
      rw [← idealHeight_eq_coheight, hx, Ideal.height_bot]
      decide
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hc, Int.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro P _
    apply Finsupp.single_eq_of_ne
    intro h
    exact P.ne_bot ((congrArg PrimeSpectrum.asIdeal h.symm).trans hx)
  · let P : HeightOneSpectrum S := ⟨x.asIdeal, x.isPrime, hx⟩
    have he : AffineOrder.BundleCycles.normalBranchPoint S P = x := rfl
    rw [← he]
    rw [Finset.sum_eq_single P]
    · exact Finsupp.single_eq_same.symm
    · intro Q _ hQP
      exact Finsupp.single_eq_of_ne (fun h => hQP (normalBranchPoint_injective S h.symm))
    · simp

theorem normalBranch_mapsToClosedPoint (R : Type) [CommRing R] [IsLocalRing R]
    [Algebra R S] [Module.Finite R S] (P : HeightOneSpectrum S) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) (AffineOrder.BundleCycles.normalBranchPoint S P) =
      (IsLocalRing.closedPoint R : Spec (CommRingCat.of R)) := by
  apply PrimeSpectrum.ext
  exact IsLocalRing.eq_maximalIdeal (inferInstanceAs (P.asIdeal.under R).IsMaximal)

theorem normalPrincipalPointDivisor_pushforward (R : Type)
    [CommRing R] [IsLocalRing R] [Algebra R S] [Module.Finite R S]
    [Fintype (HeightOneSpectrum S)] (g : (Spec (CommRingCat.of S)).functionField) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (CommRingCat.of S)) g) =
        Finsupp.single (IsLocalRing.closedPoint R : Spec (CommRingCat.of R))
          (∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℚ) *
            ((Spec (CommRingCat.of S)).ord g (AffineOrder.BundleCycles.normalBranchPoint S P) : ℚ)) := by
  rw [normalPrincipalPointDivisor_eq_sum, map_sum, Finsupp.single_finsetSum]
  apply Finset.sum_congr rfl
  intro P _
  rw [IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, normalBranch_mapsToClosedPoint, Affine.ResidueDegree.BundleCycles.affineResidueDegree_eq_inertiaDeg]
  congr 1
  exact mul_comm _ _

end

/-!
# LineBundleCycles: normalized local divisors recover singular divisor coefficients

The finite normalization of a codimension-one stalk may have several
branches. Pushing its actual principal divisor to the original local
spectrum recovers the original scheme order at its closed point.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory IsDedekindDomain _root_.Order
open scoped Classical BigOperators

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

local instance (S : Type) [CommRing S] [IsDomain S] : Algebra S (Spec (CommRingCat.of S)).functionField :=
  (StructureSheaf.toStalk S (genericPoint (Spec (CommRingCat.of S)))).hom.toAlgebra

local instance (S : Type) [CommRing S] [IsDomain S] : IsFractionRing S (Spec (CommRingCat.of S)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of S)

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (x : X) (hx : coheight x = 1)

/-- The canonical identification with the normalized local spectrum's generic field. -/
def normalizedStalkFieldIso :
    X.functionField ≃+* (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))).functionField := by
  let R := X.presheaf.stalk x
  let S := integralClosure R X.functionField
  let : IsDedekindDomain S := IntersectionTheory.ProjectionFormula.Support.Normalization.stalk_normalization_isDedekind f x hx
  let : IsFractionRing S X.functionField :=
    integralClosure.isFractionRing_of_finite_extension X.functionField X.functionField
  exact (FractionRing.algEquiv S X.functionField).symm.toRingEquiv.trans (AffineOrder.BundleCycles.normalAffineFieldIso S).toRingEquiv

theorem normalizedLocal_principalDivisor_pushforward (g : X.functionField) (hg : g ≠ 0) :
    letI : IsDedekindDomain (integralClosure (X.presheaf.stalk x) X.functionField) :=
      IntersectionTheory.ProjectionFormula.Support.Normalization.stalk_normalization_isDedekind f x hx
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x)
        (integralClosure (X.presheaf.stalk x) X.functionField))))
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor
        (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField)))
        (normalizedStalkFieldIso X f x hx g)) =
      Finsupp.single (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x))
        (X.ord g x : ℚ) := by
  let R := X.presheaf.stalk x
  let S := integralClosure R X.functionField
  let : IsDedekindDomain S := IntersectionTheory.ProjectionFormula.Support.Normalization.stalk_normalization_isDedekind f x hx
  let : Module.Finite R S := IntersectionTheory.ProjectionFormula.Support.Normalization.finite_stalk_normalization f x
  let : IsFractionRing S X.functionField :=
    integralClosure.isFractionRing_of_finite_extension X.functionField X.functionField
  let : Finite (HeightOneSpectrum S) := IntersectionTheory.ProjectionFormula.BranchOrder.finite_heightOneSpectrum R S
  let := Fintype.ofFinite (HeightOneSpectrum S)
  rw [normalPrincipalPointDivisor_pushforward]
  congr 1
  rw [NormalizedBranchOrder.BundleCycles.schemeOrd_eq_normalizedBranchOrderSum X f x hx g hg]
  change (∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℚ) *
    ((Spec (CommRingCat.of S)).ord
      (AffineOrder.BundleCycles.normalAffineFieldIso S ((FractionRing.algEquiv S X.functionField).symm g))
      (AffineOrder.BundleCycles.normalBranchPoint S P) : ℚ)) =
    ((∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℤ) *
      IntersectionTheory.ProjectionFormula.SemilocalDivisorNorm.localOrder P ((FractionRing.algEquiv S X.functionField).symm g) : ℤ) : ℚ)
  simp only [AffineOrder.BundleCycles.schemeOrder_eq_normalBranchOrder, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.BranchPushforward.BundleCycles
