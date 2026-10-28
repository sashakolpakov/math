import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorExtraction
import Mathlib.RingTheory.Derivation.Basic

/-! # Factor Uniqueness -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorUniqueness.Construction

noncomputable section

/-! Uniqueness of regular prime boundary factors and of the residual ideal. -/

variable {R : Type*} [CommRing R]

/-- A regular principal factor can be cancelled in an inclusion of ideals. -/
theorem regular_principal_mul_le_iff (c : R) (hc : IsRegular c) (I J : Ideal R) :
    Ideal.span {c} * I ≤ Ideal.span {c} * J ↔ I ≤ J := by
  constructor
  · intro h
    have he := Submodule.colon_mono h (le_refl (Ideal.span {c}))
    rwa [ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular I c hc, ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular J c hc] at he
  · exact Ideal.mul_mono le_rfl

/-- A prime boundary factor has exactly the displayed exponent if the
remaining scalar and residual ideal are not divisible by that boundary. -/
theorem prime_boundary_factor_exact_exponent (z m : R) (e : ℕ) (L : Ideal R)
    (hz : IsRegular z) (hp : (Ideal.span {z}).IsPrime)
    (hm : m ∉ Ideal.span {z}) (hL : ¬ L ≤ Ideal.span {z}) :
    Ideal.span {z ^ e} * (Ideal.span {m} * L) ≤ Ideal.span {z} ^ e ∧
      ¬ Ideal.span {z ^ e} * (Ideal.span {m} * L) ≤ Ideal.span {z} ^ (e + 1) := by
  constructor
  · rw [Ideal.span_singleton_pow]
    exact Ideal.mul_le_left
  · intro h
    rw [pow_succ, Ideal.span_singleton_pow] at h
    have hml := (regular_principal_mul_le_iff (z ^ e) (hz.pow e) _ _).mp h
    rcases hp.mul_le.mp hml with hm' | hL'
    · exact hm ((Ideal.span_singleton_le_iff_mem _).mp hm')
    · exact hL hL'

/-- The exact exponent in an ideal-power filtration is unique. -/
theorem exact_ideal_power_exponent_unique (I J : Ideal R) (a b : ℕ)
    (ha : J ≤ I ^ a) (ha1 : ¬ J ≤ I ^ (a + 1))
    (hb : J ≤ I ^ b) (hb1 : ¬ J ≤ I ^ (b + 1)) : a = b := by
  apply Nat.le_antisymm
  · by_contra h
    exact hb1 (ha.trans (Ideal.pow_le_pow_right (by omega)))
  · by_contra h
    exact ha1 (hb.trans (Ideal.pow_le_pow_right (by omega)))

variable {ι : Type*} [DecidableEq ι]

/-- Every exponent in a prime boundary factorization is the exact
order with respect to that boundary ideal. -/
theorem finite_prime_boundary_factor_exact_exponent
    (s : Finset ι) (z : ι → R) (a : ι → ℕ) (L : Ideal R) (i : ι) (hi : i ∈ s)
    (hz : IsRegular (z i)) (hp : (Ideal.span {z i}).IsPrime)
    (hind : ∀ j ∈ s, j ≠ i → z j ∉ Ideal.span {z i})
    (hL : ¬ L ≤ Ideal.span {z i}) :
    Ideal.span {∏ j ∈ s, z j ^ a j} * L ≤ Ideal.span {z i} ^ a i ∧
      ¬ Ideal.span {∏ j ∈ s, z j ^ a j} * L ≤ Ideal.span {z i} ^ (a i + 1) := by
  let P := Ideal.span {z i}
  let : P.IsPrime := hp
  have hm : (∏ j ∈ s.erase i, z j ^ a j) ∉ P := by
    apply P.primeCompl.prod_mem
    intro j hj
    exact P.primeCompl.pow_mem (hind j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)) _
  have he : (∏ j ∈ s, z j ^ a j) = z i ^ a i * ∏ j ∈ s.erase i, z j ^ a j :=
    (Finset.mul_prod_erase s (fun j => z j ^ a j) hi).symm
  rw [he, ← Ideal.span_singleton_mul_span_singleton, mul_assoc]
  exact prime_boundary_factor_exact_exponent (z i) _ (a i) L hz hp hm hL

/-- Residual primitivity makes the boundary exponents independent of the
order in which the factors were extracted. -/
theorem finite_prime_boundary_exponents_unique
    (s : Finset ι) (z : ι → R) (a b : ι → ℕ) (L M : Ideal R)
    (hreg : ∀ i ∈ s, IsRegular (z i))
    (hprime : ∀ i ∈ s, (Ideal.span {z i}).IsPrime)
    (hind : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → z j ∉ Ideal.span {z i})
    (hL : ∀ i ∈ s, ¬ L ≤ Ideal.span {z i}) (hM : ∀ i ∈ s, ¬ M ≤ Ideal.span {z i})
    (he : Ideal.span {∏ i ∈ s, z i ^ a i} * L = Ideal.span {∏ i ∈ s, z i ^ b i} * M) :
    ∀ i ∈ s, a i = b i := by
  intro i hi
  have ha := finite_prime_boundary_factor_exact_exponent s z a L i hi
    (hreg i hi) (hprime i hi) (hind i hi) (hL i hi)
  have hb := finite_prime_boundary_factor_exact_exponent s z b M i hi
    (hreg i hi) (hprime i hi) (hind i hi) (hM i hi)
  rw [← he] at hb
  exact exact_ideal_power_exponent_unique _ _ (a i) (b i) ha.1 ha.2 hb.1 hb.2

omit [DecidableEq ι] in
/-- Once the exponents agree, regularity determines the residual ideal uniquely. -/
theorem finite_regular_boundary_residual_unique
    (s : Finset ι) (z : ι → R) (a b : ι → ℕ) (L M : Ideal R)
    (hreg : ∀ i ∈ s, IsRegular (z i)) (hab : ∀ i ∈ s, a i = b i)
    (he : Ideal.span {∏ i ∈ s, z i ^ a i} * L = Ideal.span {∏ i ∈ s, z i ^ b i} * M) :
    L = M := by
  have hprod : (∏ i ∈ s, z i ^ a i) = ∏ i ∈ s, z i ^ b i :=
    Finset.prod_congr rfl (fun i hi => congrArg (fun n => z i ^ n) (hab i hi))
  rw [← hprod] at he
  have hregular : IsRegular (∏ i ∈ s, z i ^ a i) :=
    IsRegular.prod (fun i hi => (hreg i hi).pow (a i))
  exact le_antisymm
    ((regular_principal_mul_le_iff _ hregular L M).mp he.le)
    ((regular_principal_mul_le_iff _ hregular M L).mp he.ge)

variable {k : Type*} [CommRing k] [Algebra k R]

/-- Dual coordinate derivatives rule out divisibility of one coordinate
by another through the point. -/
theorem transverse_coordinate_not_mem_span (D : Derivation k R R) (z w : R)
    (hDz : D z = 0) (hDw : D w = 1) (q : Ideal R) (hq : q ≠ ⊤) (hzq : z ∈ q) :
    w ∉ Ideal.span {z} := by
  intro hw
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hw
  have hmem : D w ∈ q := by
    rw [ha, D.leibniz, hDz, smul_zero, add_zero]
    exact q.mul_mem_right (D a) hzq
  rw [hDw] at hmem
  exact hq (Ideal.eq_top_of_isUnit_mem q hmem isUnit_one)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorUniqueness.Construction
