import OAI.NumberTheory.Adeles.LocalCompletions

/-! # Finite Character -/

namespace OAI.NumberTheory.Adeles.FiniteCharacter.CompletionFactors

noncomputable section

section

/-! The fractional ideal of a finite idele and principal powers. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology WithZero nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

def finiteIdeleOrder (a : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : ℤ :=
  -WithZero.log (Valued.v (a.val v))

theorem finiteIdeleOrder_support (a : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, finiteIdeleOrder a v = 0 := by
  filter_upwards [FiniteAdeleRing.unitsEquiv_finite_valued_eq_one a] with v hv
  change Valued.v (a.val v) = 1 at hv
  simp [finiteIdeleOrder, hv]

def finiteIdeleIdeal (a : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ finiteIdeleOrder a v

theorem finiteIdeleIdeal_ne_zero (a : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ) : finiteIdeleIdeal a ≠ 0 := by
  apply finprod_ne_zero
  intro v
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

theorem finiteIdeleIdeal_count (a : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (finiteIdeleIdeal a) = finiteIdeleOrder a v :=
  FractionalIdeal.count_finprod K v _ (finiteIdeleOrder_support a)

theorem count_spanSingleton_integer (v : HeightOneSpectrum (𝓞 K))
    (a : 𝓞 K) (ha : a ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) =
      -WithZero.log (v.valuation K (a : K)) := by
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v (J := Ideal.span {a}) (by simpa using ha), valuation_of_algebraMap,
    intValuation_if_neg _ ha, WithZero.log_exp, neg_neg]

theorem count_spanSingleton (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) =
      -WithZero.log (v.valuation K x) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : a ≠ 0 := by
    intro h
    apply hx
    rw [← hab, h, map_zero, zero_div]
  rw [← hab, ← FractionalIdeal.spanSingleton_div_spanSingleton, div_eq_mul_inv,
    FractionalIdeal.count_mul _ _ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (RingOfIntegers.coe_ne_zero_iff.mpr ha)) (inv_ne_zero
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr hb0))),
    FractionalIdeal.count_inv, count_spanSingleton_integer v a ha,
    count_spanSingleton_integer v b hb0, map_div₀,
    WithZero.log_div ((Valuation.ne_zero_iff _).mpr (RingOfIntegers.coe_ne_zero_iff.mpr ha))
      ((Valuation.ne_zero_iff _).mpr (RingOfIntegers.coe_ne_zero_iff.mpr hb0))]
  ring

theorem fractionalIdeal_exists_principal_power (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∃ (n : ℕ) (x : Kˣ), 0 < n ∧ I ^ n = FractionalIdeal.spanSingleton (𝓞 K)⁰ x.val := by
  let u : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 I hI
  let n := Fintype.card (ClassGroup (𝓞 K))
  have hp : (↑(u ^ n) : Submodule (𝓞 K) K).IsPrincipal := by
    apply ClassGroup.mk_eq_one_iff.mp
    rw [map_pow]
    exact pow_card_eq_one
  obtain ⟨x, hx⟩ := hp.principal
  have he : I ^ n = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    change (I ^ n : Submodule (𝓞 K) K) =
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x : Submodule (𝓞 K) K)
    rw [FractionalIdeal.coe_spanSingleton]
    simp only [Units.val_pow_eq_pow_val, u, Units.val_mk0] at hx
    exact hx
  have hx0 : x ≠ 0 := by
    intro h
    apply pow_ne_zero n hI
    simpa [h] using he
  exact ⟨n, Units.mk0 x hx0, Fintype.card_pos, he⟩

theorem finiteIdele_exists_principal_power (a : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ) :
    ∃ (n : ℕ) (x : Kˣ), 0 < n ∧
      ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (a.val v) ^ n = v.valuation K x.val := by
  obtain ⟨n, x, hn, hx⟩ := fractionalIdeal_exists_principal_power
    (finiteIdeleIdeal a) (finiteIdeleIdeal_ne_zero a)
  refine ⟨n, x, hn, fun v => ?_⟩
  have hv0 : Valued.v (a.val v) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (Units.ne_zero (RestrictedProduct.unitsEquiv _ a v))
  have hx0 : v.valuation K x.val ≠ 0 := (Valuation.ne_zero_iff _).mpr x.ne_zero
  have hc := congrArg (FractionalIdeal.count K v) hx
  rw [FractionalIdeal.count_pow, finiteIdeleIdeal_count, count_spanSingleton v x.val x.ne_zero,
    finiteIdeleOrder, mul_neg] at hc
  have hlog : WithZero.log (Valued.v (a.val v) ^ n) = WithZero.log (v.valuation K x.val) := by
    rw [WithZero.log_pow, nsmul_eq_mul]
    exact neg_injective hc
  have he := congrArg WithZero.exp hlog
  simpa only [WithZero.exp_log (pow_ne_zero n hv0), WithZero.exp_log hx0] using he

end

/-! Finite idele characters are determined by principal ideles and integral units. -/

open _root_.NumberField IsDedekindDomain HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology WithZero NNReal

variable {K : Type*} [Field K] [NumberField K]

def finitePrincipal : Kˣ →* (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ :=
  Units.map (algebraMap K (LocalCompletions.CompletionFactors.FiniteAdele K)).toMonoidHom

theorem finiteIdele_exists_principal_unit_power (a : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ) :
    ∃ (n : ℕ) (x : Kˣ) (u : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ), 0 < n ∧
      a ^ n = u * finitePrincipal x ∧
      ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (u.val v) = 1 := by
  obtain ⟨n, x, hn, hv⟩ := finiteIdele_exists_principal_power a
  let u := a ^ n / finitePrincipal x
  refine ⟨n, x, u, hn, (div_mul_cancel _ _).symm, fun v => ?_⟩
  have he : u.val v = a.val v ^ n / algebraMap K (v.adicCompletion K) x.val := by
    let ev : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ →* (v.adicCompletion K)ˣ :=
      Units.map (RestrictedProduct.evalMonoidHom (fun w : HeightOneSpectrum (𝓞 K) =>
        w.adicCompletion K) v)
    have h := congrArg Units.val (map_div ev (a ^ n) (finitePrincipal x))
    rw [map_pow, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] at h
    exact h
  rw [he, map_div₀, map_pow, hv]
  change v.valuation K x.val / Valued.v (x.val : v.adicCompletion K) = 1
  rw [adicCompletion.valued_coe]
  exact div_self ((Valuation.ne_zero_iff _).mpr x.ne_zero)

theorem finiteIdele_integral_of_valuation_one (a : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ)
    (ha : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (a.val v) = 1) :
    (∀ v : HeightOneSpectrum (𝓞 K), a.val v ∈ v.adicCompletionIntegers K) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), a.inv v ∈ v.adicCompletionIntegers K) := by
  constructor
  · intro v
    exact (ha v).le
  · intro v
    have hi : a.inv v = (a.val v)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      exact congrArg (fun b : LocalCompletions.CompletionFactors.FiniteAdele K => b v) a.inv_val
    change Valued.v (a.inv v) ≤ 1
    rw [hi, map_inv₀, ha v, inv_one]

theorem finiteCharacter_eq (p q : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ →* ℝ≥0)
    (hp : ∀ u : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ,
      (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (u.val v) = 1) → p u = 1)
    (hq : ∀ u : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ,
      (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (u.val v) = 1) → q u = 1)
    (hprincipal : ∀ x : Kˣ, p (finitePrincipal x) = q (finitePrincipal x))
    (a : (LocalCompletions.CompletionFactors.FiniteAdele K)ˣ) : p a = q a := by
  obtain ⟨n, x, u, hn, he, hu⟩ := finiteIdele_exists_principal_unit_power a
  have hpow : p a ^ n = q a ^ n := by
    rw [← map_pow, ← map_pow, he, map_mul, map_mul, hp u hu, hq u hu,
      one_mul, one_mul, hprincipal]
  exact (pow_left_injective hn.ne') hpow

end

end OAI.NumberTheory.Adeles.FiniteCharacter.CompletionFactors
