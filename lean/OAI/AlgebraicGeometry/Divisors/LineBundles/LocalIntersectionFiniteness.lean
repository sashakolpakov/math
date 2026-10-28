import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalIntersectionLength
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.HopkinsLevitzki

/-! # Local Intersection Finiteness -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalIntersectionFiniteness.BundleCycles

noncomputable section

/-!
# LineBundleCycles: local intersection finiteness from the actual zero locus

In a Noetherian local ring an ideal with radical equal to the maximal
ideal has a finite-length quotient. Applied to the actual two-equation
ideal, this supplies the finiteness used by the symmetric intersection
invariant without assuming a multiplicity or length comparison.
-/

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem finiteLength_quotient_of_radical_maximal (I : Ideal R)
    (hI : I.radical = IsLocalRing.maximalIdeal R) : IsFiniteLength R (R ⧸ I) := by
  have hmin : I.minimalPrimes = {IsLocalRing.maximalIdeal R} := by
    rw [← Ideal.radical_minimalPrimes, hI, Ideal.minimalPrimes_eq_subsingleton_self]
  have : Ring.KrullDimLE 0 (R ⧸ I) :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr (by
      intro J hJ
      rw [hmin, Set.mem_singleton_iff] at hJ
      subst J
      infer_instance)
  let : IsNoetherianRing (R ⧸ I) :=
    isNoetherianRing_of_surjective R (R ⧸ I) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsArtinianRing (R ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_quotient I, isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))⟩

/-- The actual local intersection number when the two-equation zero locus is the closed point. -/
def closedPointIntersectionLength (a b : R)
    (h : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R) : ℤ :=
  LocalIntersectionLength.BundleCycles.localIntersectionLength a b (finiteLength_quotient_of_radical_maximal (Ideal.span {a, b}) h)

theorem closedPointIntersectionLength_comm [IsDomain R] (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : (Ideal.span {a, b}).radical = IsLocalRing.maximalIdeal R)
    (hba : (Ideal.span {b, a}).radical = IsLocalRing.maximalIdeal R) :
    closedPointIntersectionLength a b hab = closedPointIntersectionLength b a hba :=
  LocalIntersectionLength.BundleCycles.localIntersectionLength_comm a b ha hb (finiteLength_quotient_of_radical_maximal (Ideal.span {a, b}) hab)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalIntersectionFiniteness.BundleCycles
