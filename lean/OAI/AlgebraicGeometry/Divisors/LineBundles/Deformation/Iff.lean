import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.Cone
import Mathlib.Algebra.Polynomial.Laurent

/-! # Iff -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Iff.BundleCycles

noncomputable section

/-!
# LineBundleCycles: affine deformation to the normal cone

The extended Rees algebra is the subalgebra R[t,I/t] of R[t,t⁻¹]. Its
coefficient at exponent n lies in I^max(-n,0). This construction retains the
actual ideal and supplies the deformation parameter, rather than postulating
a specialization map on cycles.
-/

open LaurentPolynomial

universe u
variable {R : Type u} [CommRing R]

/-- The extended Rees algebra, with positive parameter t. -/
def deformationAlgebra (I : Ideal R) : Subalgebra R (LaurentPolynomial R) where
  carrier := {p | ∀ n : ℤ, p.coeff n ∈ I ^ (-n).toNat}
  mul_mem' {p q} hp hq n := by
    rw [AddMonoidAlgebra.coeff_mul_apply_left]
    apply Ideal.sum_mem
    intro m hm
    have h := Ideal.mul_mem_mul (hp m) (hq (-m + n))
    rw [← pow_add] at h
    exact Ideal.pow_le_pow_right (by omega) h
  one_mem' n := by
    change (AddMonoidAlgebra.single 0 (1 : R)).coeff n ∈ _
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · subst n
      simp
    · exact Ideal.zero_mem _
  add_mem' hp hq n := Ideal.add_mem _ (hp n) (hq n)
  zero_mem' _ := Ideal.zero_mem _
  algebraMap_mem' r n := by
    change (AddMonoidAlgebra.single 0 r).coeff n ∈ _
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h
    · subst n
      simp
    · exact Ideal.zero_mem _

theorem mem_deformationAlgebra_iff (I : Ideal R) (p : LaurentPolynomial R) :
    p ∈ deformationAlgebra I ↔ ∀ n : ℤ, p.coeff n ∈ I ^ (-n).toNat := Iff.rfl

/-- Exact coefficient condition for a Laurent monomial. -/
theorem single_mem_deformationAlgebra_iff (I : Ideal R) (n : ℤ) (r : R) :
    AddMonoidAlgebra.single n r ∈ deformationAlgebra I ↔ r ∈ I ^ (-n).toNat := by
  classical
  constructor
  · intro h
    simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using h n
  · intro h m
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with hnm
    · simpa [← hnm] using h
    · exact Ideal.zero_mem _

/-- A monomial together with its ideal-power membership. -/
def deformationMonomial (I : Ideal R) (n : ℤ) (r : R)
    (hr : r ∈ I ^ (-n).toNat) : deformationAlgebra I :=
  ⟨AddMonoidAlgebra.single n r,
    (single_mem_deformationAlgebra_iff I n r).mpr hr⟩

/-- The regular parameter t of the deformation. -/
def deformationParameter (I : Ideal R) : deformationAlgebra I :=
  deformationMonomial I 1 1 (by simp)

@[simp]
theorem deformationParameter_val (I : Ideal R) :
    (deformationParameter I : LaurentPolynomial R) = T 1 := rfl

/-- Multiplication by t shifts the Laurent coefficient by one. -/
theorem deformationParameter_mul_coeff (I : Ideal R) (p : deformationAlgebra I) (n : ℤ) :
    ((deformationParameter I * p : deformationAlgebra I) : LaurentPolynomial R).coeff n =
      (p : LaurentPolynomial R).coeff (n - 1) := by
  change (AddMonoidAlgebra.single 1 1 * p.val).coeff n = _
  simp only [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1
  omega

/-- The parameter is a non-zero-divisor, including over rings with zero divisors. -/
theorem deformationParameter_regular (I : Ideal R) :
    deformationParameter I ∈ nonZeroDivisors (deformationAlgebra I) := by
  have hregular : ∀ p : deformationAlgebra I, deformationParameter I * p = 0 → p = 0 := by
    intro p hp
    apply Subtype.ext
    ext n
    have h := congrArg (fun q : deformationAlgebra I => q.val.coeff (n + 1)) hp
    rw [deformationParameter_mul_coeff] at h
    simpa using h
  exact mem_nonZeroDivisors_iff.mpr ⟨hregular, fun p hp => hregular p (by rwa [mul_comm])⟩

/-- The ideal of the special fiber t = 0. -/
def deformationSpecialIdeal (I : Ideal R) : Ideal (deformationAlgebra I) :=
  Ideal.span {deformationParameter I}

/-- Dividing a Laurent polynomial by t increases the required ideal power
by one at every nonpositive exponent. -/
theorem mem_deformationSpecialIdeal_iff (I : Ideal R) (p : deformationAlgebra I) :
    p ∈ deformationSpecialIdeal I ↔
      ∀ n : ℤ, p.val.coeff n ∈ I ^ (1 - n).toNat := by
  rw [deformationSpecialIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, rfl⟩ n
    rw [deformationParameter_mul_coeff]
    convert q.property (n - 1) using 1
    congr 2
    omega
  · intro hp
    let q : deformationAlgebra I := ⟨T (-1) * p.val, fun n => by
      change (AddMonoidAlgebra.single (-1) 1 * p.val).coeff n ∈ _
      rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
      convert hp (-(-1) + n) using 1
      congr 2
      omega⟩
    refine ⟨q, Subtype.ext ?_⟩
    change p.val = T 1 * (T (-1) * p.val)
    rw [← mul_assoc, ← T_add]
    simp only [Int.reduceAdd, T_zero, one_mul]

/-- Coefficients of an ordinary polynomial after Laurent extension. -/
theorem toLaurent_coeff_nat (p : Polynomial R) (n : ℕ) :
    p.toLaurent.coeff (n : ℤ) = p.coeff n := by
  rw [coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective _ n

theorem toLaurent_coeff_neg (p : Polynomial R) (n : ℤ) (hn : n < 0) :
    p.toLaurent.coeff n = 0 := by
  rw [coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, hm⟩
  have : (m : ℤ) = n := hm
  omega

/-- The Rees algebra embeds in the deformation by reversing the exponent:
a degree-n coefficient a maps to a/t^n. -/
def reesToDeformation (I : Ideal R) : reesAlgebra I →ₐ[R] deformationAlgebra I :=
  ((invert.toAlgHom.comp Polynomial.toLaurentAlg).comp (reesAlgebra I).val).codRestrict
    (deformationAlgebra I) (fun p n => by
      change (invert p.val.toLaurent).coeff n ∈ _
      rw [invert_apply]
      by_cases hn : 0 ≤ -n
      · have he : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg hn
        rw [← he, toLaurent_coeff_nat]
        exact p.property _
      · rw [toLaurent_coeff_neg _ _ (by omega)]
        exact Ideal.zero_mem _)

@[simp]
theorem reesToDeformation_val (I : Ideal R) (p : reesAlgebra I) :
    (reesToDeformation I p).val = invert p.val.toLaurent := rfl

theorem reesToDeformation_coeff (I : Ideal R) (p : reesAlgebra I) (n : ℕ) :
    (reesToDeformation I p).val.coeff (-(n : ℤ)) = p.val.coeff n := by
  rw [reesToDeformation_val, invert_apply, neg_neg, toLaurent_coeff_nat]

theorem reesToDeformation_coeff_pos (I : Ideal R) (p : reesAlgebra I)
    (n : ℤ) (hn : 0 < n) : (reesToDeformation I p).val.coeff n = 0 := by
  rw [reesToDeformation_val, invert_apply, toLaurent_coeff_neg _ _ (by omega)]

theorem reesToDeformation_injective (I : Ideal R) :
    Function.Injective (reesToDeformation I) := by
  intro p q h
  apply Subtype.ext
  exact Polynomial.toLaurent_injective
    (invert.injective (congrArg Subtype.val h))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Iff.BundleCycles
