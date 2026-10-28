import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteNormPadicComparison
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteCompletionNorm

/-! # Padic Embedding Mem -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PadicEmbeddingMem.Realization

noncomputable section

section

/-! Valuation bounds on conjugates imply p-adic bounds for the actual rational scalar matrix. -/

open scoped Classical _root_.Matrix
open IsDedekindDomain _root_.NumberField

theorem rational_matrix_power_bound_transfer
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] (w : HeightOneSpectrum (𝓞 E))
    (p : ℕ) [Fact p.Prime] (hpw : (p : 𝓞 E) ∈ w.asIdeal)
    {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℚ) (R : ℝ)
    (hR : ∀ (N : ℕ) i j, ‖(A.map (algebraMap ℚ (w.adicCompletion E)) ^ N) i j‖ ≤ R) :
    ∃ T : ℝ, ∀ (N : ℕ) i j, ‖(A.map (algebraMap ℚ ℚ_[p]) ^ N) i j‖ ≤ T := by
  obtain ⟨c, hc, he⟩ := FiniteNormPadicComparison.Realization.finite_norm_padic_rpow E w p hpw
  refine ⟨R ^ c, ?_⟩
  intro N i j
  rw [← Matrix.map_pow, Matrix.map_apply]
  change ‖((A ^ N) i j : ℚ_[p])‖ ≤ _
  rw [← he]
  have h := hR N i j
  rw [← Matrix.map_pow, Matrix.map_apply] at h
  exact Real.rpow_le_rpow (norm_nonneg _) h hc.le

theorem rational_scalar_padic_power_bounds
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) [Fact p.Prime]
    (hpw : (p : 𝓞 E) ∈ w.asIdeal) {I : Type*} [Fintype I] [DecidableEq I]
    (e : (Fin 3 → E) ≃ₗ[ℚ] (I → ℚ)) (r : E)
    (hr : ∀ σ : E ≃ₐ[ℚ] E, w.valuation E (σ r) ≤ 1) :
    ∃ R : ℝ, ∀ (N : ℕ) i j,
      ‖((RationalCoordinates.Realization.rationalScalarMatrix E e r).map (algebraMap ℚ ℚ_[p]) ^ N) i j‖ ≤ R := by
  obtain ⟨R, hR⟩ := FiniteCompletionNorm.Realization.rational_scalar_finite_completion_bounds E w e r hr
  exact rational_matrix_power_bound_transfer E w p hpw _ R hR

end

section

/-! Pulling back a finite prime transports local integrality of the CM scalar. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]

def galoisPrimePullback (w : HeightOneSpectrum (𝓞 E)) (σ : E ≃ₐ[ℚ] E) : HeightOneSpectrum (𝓞 E) where
  asIdeal := Ideal.comap (RingOfIntegers.mapRingEquiv σ.toRingEquiv).toRingHom w.asIdeal
  isPrime := w.isPrime.comap _
  ne_bot := fun h => w.ne_bot (Ideal.eq_bot_of_comap_eq_bot'
    (RingOfIntegers.mapRingEquiv σ.toRingEquiv).surjective h)

omit [NumberField E] in
theorem galoisPrimePullback_nat_mem (w : HeightOneSpectrum (𝓞 E)) (σ : E ≃ₐ[ℚ] E) (p : ℕ) :
    (p : 𝓞 E) ∈ (galoisPrimePullback E w σ).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  change (RingOfIntegers.mapRingEquiv σ.toRingEquiv) (p : 𝓞 E) ∈ w.asIdeal ↔ _
  rw [map_natCast]

theorem valuation_conjugate_le_one (w : HeightOneSpectrum (𝓞 E)) (σ : E ≃ₐ[ℚ] E)
    (r : E) (hr : (galoisPrimePullback E w σ).valuation E r ≤ 1) :
    w.valuation E (σ r) ≤ 1 := by
  obtain ⟨n, d, hnd⟩ := (galoisPrimePullback E w σ).exists_primeCompl_mul_eq_of_integer r hr
  let σR := RingOfIntegers.mapRingEquiv σ.toRingEquiv
  have hd : σR d.val ∉ w.asIdeal := d.property
  have hdv : w.valuation E (σ (algebraMap (𝓞 E) E d.val)) = 1 :=
    (w.valuation_eq_one_iff_notMem).mpr hd
  have hn : w.valuation E (σ (algebraMap (𝓞 E) E n)) ≤ 1 := w.valuation_le_one (σR n)
  have he := congrArg (w.valuation E) (congrArg σ hnd)
  simp only [map_mul] at he
  rw [hdv, mul_one] at he
  exact he.trans_le hn

omit [NumberField E] [Algebra ℚ E] in
theorem finite_prime_natPrime_unique (w : HeightOneSpectrum (𝓞 E))
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : (p : 𝓞 E) ∈ w.asIdeal) (hq : (q : 𝓞 E) ∈ w.asIdeal) : p = q := by
  by_contra hpq
  have hcop : Nat.Coprime p q := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
    intro hd
    exact hpq (((Nat.dvd_prime (Fact.out : q.Prime)).mp hd).resolve_left (Fact.out : p.Prime).ne_one))
  obtain ⟨a, b, hab⟩ := hcop.cast (R := 𝓞 E)
  have h1 := w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hp) (w.asIdeal.mul_mem_left b hq)
  rw [hab] at h1
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem w.asIdeal h1 isUnit_one)

end

section

/-! Two-prime support gives local integrality of every conjugate away from the supporting rational prime. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField

theorem conjugates_integral_away_support
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    (q p : ℕ) [Fact q.Prime] [Fact p.Prime] (hpq : p ≠ q)
    (w₀ w₁ w : HeightOneSpectrum (𝓞 E))
    (hq₀ : (q : 𝓞 E) ∈ w₀.asIdeal) (hq₁ : (q : 𝓞 E) ∈ w₁.asIdeal)
    (hpw : (p : 𝓞 E) ∈ w.asIdeal) (r : E)
    (hr : ∀ v : HeightOneSpectrum (𝓞 E), v ≠ w₀ → v ≠ w₁ → v.valuation E r = 1) :
    ∀ σ : E ≃ₐ[ℚ] E, w.valuation E (σ r) ≤ 1 := by
  intro σ
  apply valuation_conjugate_le_one E w σ r
  have hwp : (p : 𝓞 E) ∈ (galoisPrimePullback E w σ).asIdeal :=
    (galoisPrimePullback_nat_mem E w σ p).mpr hpw
  have hne₀ : galoisPrimePullback E w σ ≠ w₀ := by
    intro he
    rw [he] at hwp
    exact hpq (finite_prime_natPrime_unique E w₀ p q hwp hq₀)
  have hne₁ : galoisPrimePullback E w σ ≠ w₁ := by
    intro he
    rw [he] at hwp
    exact hpq (finite_prime_natPrime_unique E w₁ p q hwp hq₁)
  exact (hr _ hne₀ hne₁).le

theorem rational_scalar_away_support_power_bounds
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    (q p : ℕ) [Fact q.Prime] [Fact p.Prime] (hpq : p ≠ q)
    (w₀ w₁ w : HeightOneSpectrum (𝓞 E))
    (hq₀ : (q : 𝓞 E) ∈ w₀.asIdeal) (hq₁ : (q : 𝓞 E) ∈ w₁.asIdeal)
    (hpw : (p : 𝓞 E) ∈ w.asIdeal) {I : Type*} [Fintype I] [DecidableEq I]
    (e : (Fin 3 → E) ≃ₗ[ℚ] (I → ℚ)) (r : E)
    (hr : ∀ v : HeightOneSpectrum (𝓞 E), v ≠ w₀ → v ≠ w₁ → v.valuation E r = 1) :
    ∃ R : ℝ, ∀ (N : ℕ) i j,
      ‖((RationalCoordinates.Realization.rationalScalarMatrix E e r).map (algebraMap ℚ ℚ_[p]) ^ N) i j‖ ≤ R :=
  rational_scalar_padic_power_bounds E w p hpw e r
    (conjugates_integral_away_support E q p hpq w₀ w₁ w hq₀ hq₁ hpw r hr)

end

section

/-! Every rational prime has a finite prime above it in a number field. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField

theorem exists_finite_prime_above_rational (E : Type*) [Field E] [NumberField E]
    (p : ℕ) [Fact p.Prime] : ∃ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal := by
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let : P.IsPrime := (Ideal.span_singleton_prime hp0).mpr
    (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 E) P (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have hpP : (p : ℤ) ∈ P := Ideal.subset_span (Set.mem_singleton _)
    rw [← hQP] at hpP
    change algebraMap ℤ (𝓞 E) (p : ℤ) ∈ Q at hpP
    simpa only [map_natCast] using hpP
  have hQ0 : Q ≠ ⊥ := by
    intro he
    rw [he, Ideal.mem_bot] at hpQ
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hpQ
  exact ⟨⟨Q, hQ, hQ0⟩, hpQ⟩

theorem rational_scalar_all_away_power_bounds
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    (q : ℕ) [Fact q.Prime] (w₀ w₁ : HeightOneSpectrum (𝓞 E))
    (hq₀ : (q : 𝓞 E) ∈ w₀.asIdeal) (hq₁ : (q : 𝓞 E) ∈ w₁.asIdeal)
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : (Fin 3 → E) ≃ₗ[ℚ] (I → ℚ)) (r : E)
    (hr : ∀ v : HeightOneSpectrum (𝓞 E), v ≠ w₀ → v ≠ w₁ → v.valuation E r = 1) :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ q → ∃ R : ℝ, ∀ (N : ℕ) i j,
      ‖((RationalCoordinates.Realization.rationalScalarMatrix E e r).map (algebraMap ℚ ℚ_[p]) ^ N) i j‖ ≤ R := by
  intro p hp hpq
  obtain ⟨w, hpw⟩ := exists_finite_prime_above_rational E p
  exact rational_scalar_away_support_power_bounds E q p hpq w₀ w₁ w hq₀ hq₁ hpw e r hr

end

section

/-! A p-adic embedding carries algebraic integers into p-adic integers. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField

variable (q : ℕ) [Fact q.Prime] {E : Type*} [Field E] [Algebra ℚ E]

theorem padic_embedding_integer_norm (σ : E →ₐ[ℚ] ℚ_[q]) (x : 𝓞 E) : ‖σ (x : E)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (σ (x : E)) := map_isIntegral_int σ.toRingHom x.property
  have hxq : IsIntegral ℤ_[q] (σ (x : E)) := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxq
  rw [← hy]
  exact y.property

def padicEmbeddingIntegers (σ : E →ₐ[ℚ] ℚ_[q]) : 𝓞 E →+* ℤ_[q] where
  toFun x := ⟨σ (x : E), padic_embedding_integer_norm q σ x⟩
  map_zero' := Subtype.ext (map_zero σ)
  map_one' := Subtype.ext (map_one σ)
  map_add' x y := Subtype.ext (map_add σ (x : E) (y : E))
  map_mul' x y := Subtype.ext (map_mul σ (x : E) (y : E))

theorem padicEmbeddingIntegers_mem_maximal (σ : E →ₐ[ℚ] ℚ_[q]) (x : 𝓞 E) :
    padicEmbeddingIntegers q σ x ∈ IsLocalRing.maximalIdeal ℤ_[q] ↔ ‖σ (x : E)‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit (padicEmbeddingIntegers q σ x) ↔ _
  rw [PadicInt.isUnit_iff]
  change ¬‖σ (x : E)‖ = 1 ↔ ‖σ (x : E)‖ < 1
  exact ((lt_iff_le_and_ne).trans (and_iff_right (padic_embedding_integer_norm q σ x))).symm

end

section

/-! The finite prime induced by an embedding into the p-adic field. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField

variable (q : ℕ) [Fact q.Prime] {E : Type*} [Field E] [Algebra ℚ E]

def padicEmbeddingIdeal (σ : E →ₐ[ℚ] ℚ_[q]) : Ideal (𝓞 E) :=
  Ideal.comap (padicEmbeddingIntegers q σ) (IsLocalRing.maximalIdeal ℤ_[q])

theorem padicEmbeddingIdeal_mem (σ : E →ₐ[ℚ] ℚ_[q]) (x : 𝓞 E) :
    x ∈ padicEmbeddingIdeal q σ ↔ ‖σ (x : E)‖ < 1 :=
  padicEmbeddingIntegers_mem_maximal q σ x

theorem padicEmbeddingIdeal_contains_prime (σ : E →ₐ[ℚ] ℚ_[q]) :
    (q : 𝓞 E) ∈ padicEmbeddingIdeal q σ := by
  rw [padicEmbeddingIdeal_mem]
  have h := Padic.norm_p_lt_one (p := q)
  simpa only [map_natCast] using h

def padicEmbeddingPrime (σ : E →ₐ[ℚ] ℚ_[q]) : HeightOneSpectrum (𝓞 E) where
  asIdeal := padicEmbeddingIdeal q σ
  isPrime := (inferInstance : (IsLocalRing.maximalIdeal ℤ_[q]).IsPrime).comap _
  ne_bot := by
    intro he
    have h := padicEmbeddingIdeal_contains_prime q σ
    rw [he, Ideal.mem_bot] at h
    have hq := congrArg (fun z : 𝓞 E => σ (z : E)) h
    change σ (q : E) = σ 0 at hq
    rw [map_natCast, map_zero] at hq
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hq

theorem padicEmbeddingPrime_contains_prime (σ : E →ₐ[ℚ] ℚ_[q]) :
    (q : 𝓞 E) ∈ (padicEmbeddingPrime q σ).asIdeal :=
  padicEmbeddingIdeal_contains_prime q σ

theorem padicEmbeddingPrime_mem (σ : E →ₐ[ℚ] ℚ_[q]) (x : 𝓞 E) :
    x ∈ (padicEmbeddingPrime q σ).asIdeal ↔ ‖σ (x : E)‖ < 1 :=
  padicEmbeddingIdeal_mem q σ x

theorem padicEmbeddingPrime_notMem (σ : E →ₐ[ℚ] ℚ_[q]) (x : 𝓞 E) :
    x ∉ (padicEmbeddingPrime q σ).asIdeal ↔ ‖σ (x : E)‖ = 1 := by
  rw [padicEmbeddingPrime_mem, not_lt]
  exact ⟨fun h => le_antisymm (padic_embedding_integer_norm q σ x) h, fun h => h.ge⟩

end

/-! The induced finite prime detects integrality under the p-adic embedding. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField

theorem valuation_le_one_of_prime_denominator
    (E : Type*) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (r : E) (n d : 𝓞 E) (hd : d ∉ w.asIdeal)
    (he : r * algebraMap (𝓞 E) E d = algebraMap (𝓞 E) E n) : w.valuation E r ≤ 1 := by
  have h := congrArg (w.valuation E) he
  rw [map_mul, (w.valuation_eq_one_iff_notMem).mpr hd, mul_one] at h
  exact h.trans_le (w.valuation_le_one n)

variable (q : ℕ) [Fact q.Prime] {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]

theorem padicEmbedding_norm_le_one_of_valuation (σ : E →ₐ[ℚ] ℚ_[q]) (r : E)
    (hr : (padicEmbeddingPrime q σ).valuation E r ≤ 1) : ‖σ r‖ ≤ 1 := by
  obtain ⟨n, d, he⟩ := (padicEmbeddingPrime q σ).exists_primeCompl_mul_eq_of_integer r hr
  have hd : ‖σ (d.val : E)‖ = 1 := (padicEmbeddingPrime_notMem q σ d.val).mp d.property
  have h := congrArg norm (congrArg σ he)
  simp only [map_mul, norm_mul] at h
  rw [hd, mul_one] at h
  exact h.trans_le (padic_embedding_integer_norm q σ n)

theorem padicEmbedding_valuation_le_one_of_norm (σ : E →ₐ[ℚ] ℚ_[q]) (r : E)
    (hr : ‖σ r‖ ≤ 1) : (padicEmbeddingPrime q σ).valuation E r ≤ 1 := by
  obtain ⟨n, d, he | he⟩ := (padicEmbeddingPrime q σ).exists_primeCompl_mul_eq_or_mul_eq r
  · exact valuation_le_one_of_prime_denominator E _ r n d.val d.property he
  · have hd : ‖σ (d.val : E)‖ = 1 := (padicEmbeddingPrime_notMem q σ d.val).mp d.property
    have h := congrArg norm (congrArg σ he)
    simp only [map_mul, norm_mul] at h
    rw [hd] at h
    have hn : ‖σ (n : E)‖ = 1 := le_antisymm (padic_embedding_integer_norm q σ n) (by
      rw [← h]
      exact mul_le_of_le_one_left (norm_nonneg _) hr)
    exact valuation_le_one_of_prime_denominator E _ r d.val n
      ((padicEmbeddingPrime_notMem q σ n).mpr hn) he

theorem padicEmbedding_valuation_le_one_iff (σ : E →ₐ[ℚ] ℚ_[q]) (r : E) :
    (padicEmbeddingPrime q σ).valuation E r ≤ 1 ↔ ‖σ r‖ ≤ 1 :=
  ⟨padicEmbedding_norm_le_one_of_valuation q σ r, padicEmbedding_valuation_le_one_of_norm q σ r⟩

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PadicEmbeddingMem.Realization
