import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Iff
import OAI.AlgebraicGeometry.Divisors.LineBundles.ReesCoefficients

/-! # Special Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiber.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the special fiber of the affine deformation

The map R[It] → R[t,I/t]/(t) sends aT^n to a/t^n. We prove its kernel
is I R[It] and its surjectivity by discarding positive Laurent exponents.
It therefore identifies the special fiber with the actual normal cone.
-/

open LaurentPolynomial

universe u
variable {R : Type u} [CommRing R]

/-- The ring of the closed fiber t = 0. -/
abbrev DeformationSpecialRing (I : Ideal R) :=
  Deformation.Iff.BundleCycles.deformationAlgebra I ⧸ Deformation.Iff.BundleCycles.deformationSpecialIdeal I

/-- The map from the ordinary Rees algebra to the special fiber. -/
def reesToSpecialFiber (I : Ideal R) : reesAlgebra I →+* DeformationSpecialRing I :=
  (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I)).comp (Deformation.Iff.BundleCycles.reesToDeformation I).toRingHom

/-- The kernel is exactly I R[It], with no regularity hypothesis on I. -/
theorem reesToSpecialFiber_ker (I : Ideal R) :
    RingHom.ker (reesToSpecialFiber I) = Normal.Cone.BundleCycles.normalConeIdeal I := by
  ext p
  change Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (Deformation.Iff.BundleCycles.reesToDeformation I p) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Deformation.Iff.BundleCycles.mem_deformationSpecialIdeal_iff,
    ReesCoefficients.BundleCycles.mem_normalConeIdeal_iff]
  constructor
  · intro h n
    have hn := h (-(n : ℤ))
    rw [Deformation.Iff.BundleCycles.reesToDeformation_coeff] at hn
    convert hn using 1
    congr 1
    omega
  · intro h n
    by_cases hn : n ≤ 0
    · have he : n = -((-n).toNat : ℤ) := by omega
      rw [he, Deformation.Iff.BundleCycles.reesToDeformation_coeff]
      convert h (-n).toNat using 1
      congr 1
      omega
    · rw [Deformation.Iff.BundleCycles.reesToDeformation_coeff_pos I p n (by omega)]
      exact Ideal.zero_mem _

/-- Truncation reads the nonnegative coefficients without alteration. -/
theorem laurentTrunc_coeff (p : LaurentPolynomial R) (n : ℕ) :
    (trunc p).coeff n = p.coeff (n : ℤ) := rfl

/-- Keep the nonpositive Laurent exponents and reverse them to Rees degrees. -/
def deformationReesTrunc (I : Ideal R) (p : Deformation.Iff.BundleCycles.deformationAlgebra I) : reesAlgebra I :=
  ⟨trunc (invert p.val), fun n => by
    rw [laurentTrunc_coeff, invert_apply]
    simpa only [neg_neg, Int.toNat_natCast] using p.property (-(n : ℤ))⟩

@[simp]
theorem deformationReesTrunc_coeff (I : Ideal R) (p : Deformation.Iff.BundleCycles.deformationAlgebra I) (n : ℕ) :
    (deformationReesTrunc I p).val.coeff n = p.val.coeff (-(n : ℤ)) := by
  change (trunc (invert p.val)).coeff n = _
  rw [laurentTrunc_coeff, invert_apply]

/-- Positive Laurent powers vanish on the special fiber. -/
theorem deformation_sub_reesTrunc_mem (I : Ideal R) (p : Deformation.Iff.BundleCycles.deformationAlgebra I) :
    p - Deformation.Iff.BundleCycles.reesToDeformation I (deformationReesTrunc I p) ∈ Deformation.Iff.BundleCycles.deformationSpecialIdeal I := by
  rw [Deformation.Iff.BundleCycles.mem_deformationSpecialIdeal_iff]
  intro n
  change p.val.coeff n - (Deformation.Iff.BundleCycles.reesToDeformation I (deformationReesTrunc I p)).val.coeff n ∈ _
  by_cases hn : n ≤ 0
  · have he : n = -((-n).toNat : ℤ) := by omega
    rw [he, Deformation.Iff.BundleCycles.reesToDeformation_coeff, deformationReesTrunc_coeff, sub_self]
    exact Ideal.zero_mem _
  · have he : (1 - n).toNat = 0 := by omega
    simp [he]

/-- Every special-fiber element has a representative in the ordinary Rees algebra. -/
theorem reesToSpecialFiber_surjective (I : Ideal R) :
    Function.Surjective (reesToSpecialFiber I) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨deformationReesTrunc I p, ?_⟩
  change Ideal.Quotient.mk _ (Deformation.Iff.BundleCycles.reesToDeformation I (deformationReesTrunc I p)) =
    Ideal.Quotient.mk _ p
  symm
  exact Ideal.Quotient.eq.mpr (deformation_sub_reesTrunc_mem I p)

/-- The affine deformation's special fiber is canonically the normal cone. -/
def normalConeSpecialFiberEquiv (I : Ideal R) :
    Normal.Cone.BundleCycles.NormalConeRing I ≃+* DeformationSpecialRing I :=
  (Ideal.quotEquivOfEq (reesToSpecialFiber_ker I).symm).trans
    (RingHom.quotientKerEquivOfSurjective (reesToSpecialFiber_surjective I))

@[simp]
theorem normalConeSpecialFiberEquiv_mk (I : Ideal R) (p : reesAlgebra I) :
    normalConeSpecialFiberEquiv I (Ideal.Quotient.mk (Normal.Cone.BundleCycles.normalConeIdeal I) p) =
      Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) (Deformation.Iff.BundleCycles.reesToDeformation I p) := by
  exact RingHom.quotientKerEquivOfSurjective_apply_mk (reesToSpecialFiber_surjective I) p

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiber.BundleCycles
