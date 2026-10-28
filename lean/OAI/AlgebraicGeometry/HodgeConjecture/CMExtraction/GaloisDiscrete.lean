import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding

/-! # Galois Discrete -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaloisDiscrete.ParameterChoices

noncomputable section

section

/-! Discrete valuation normalization is forced by surjectivity onto the
integer value group. Native local embeddings contain the rational q-powers. -/

open _root_.NumberField IsDedekindDomain
open scoped WithZero

theorem discrete_valuation_eq_of_equiv
    {F : Type*} [Field F] (v w : Valuation F ℤᵐ⁰)
    (h : v.IsEquiv w) (hv : Function.Surjective v) (hw : Function.Surjective w) : v = w := by
  obtain ⟨x, hx⟩ := hv (WithZero.exp (1 : ℤ))
  obtain ⟨y, hy⟩ := hw (WithZero.exp (1 : ℤ))
  have hvx : 1 < v x := by rw [hx, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by decide)
  have hwy : 1 < w y := by rw [hy, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by decide)
  have hwx := h.one_lt_iff_one_lt.mp hvx
  have hvy := h.one_lt_iff_one_lt.mpr hwy
  have hx0 : w x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hwx)
  have hy0 : v y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hvy)
  let m := WithZero.log (w x)
  let n := WithZero.log (v y)
  have hmx : WithZero.exp m = w x := WithZero.exp_log hx0
  have hny : WithZero.exp n = v y := WithZero.exp_log hy0
  have hm : 0 < m := by
    apply WithZero.exp_lt_exp.mp
    simpa only [WithZero.exp_zero, hmx] using hwx
  have hn : 0 < n := by
    apply WithZero.exp_lt_exp.mp
    simpa only [WithZero.exp_zero, hny] using hvy
  have hwy_pow : w (y ^ m) = w x := by
    rw [map_zpow₀, hy, ← WithZero.exp_zsmul]
    simpa only [smul_eq_mul, mul_one] using hmx
  have hvy_pow : v (y ^ m) = v x := h.eq_iff.mpr hwy_pow
  have hmn : m * n = 1 := by
    rw [map_zpow₀, ← hny, hx, ← WithZero.exp_zsmul] at hvy_pow
    exact WithZero.exp_injective hvy_pow
  have hm1 : m = 1 := by nlinarith
  have hwx1 : w x = WithZero.exp (1 : ℤ) := by rw [← hmx, hm1]
  ext a
  by_cases ha : a = 0
  · subst a
    simp
  have hva : v a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  let k := WithZero.log (v a)
  have hka : WithZero.exp k = v a := WithZero.exp_log hva
  have hpow : v (x ^ k) = v a := by
    rw [map_zpow₀, hx, ← WithZero.exp_zsmul]
    simpa only [smul_eq_mul, mul_one] using hka
  have hpoww := h.eq_iff.mp hpow
  rw [map_zpow₀, hwx1, ← WithZero.exp_zsmul] at hpoww
  exact hka.symm.trans (by simpa only [smul_eq_mul, mul_one] using hpoww)

theorem padic_mulValuation_equiv_norm (q : ℕ) [Fact q.Prime] :
    (Padic.mulValuation (p := q)).IsEquiv (NormedField.valuation (K := ℚ_[q])) := by
  classical
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  have hq : (1 : ℝ) < q := Nat.one_lt_cast.mpr (Fact.out : q.Prime).one_lt
  change Padic.mulValuation x ≤ 1 ↔ ‖x‖₊ ≤ 1
  rw [← NNReal.coe_le_coe]
  change Padic.mulValuation x ≤ 1 ↔ ‖x‖ ≤ 1
  change (if x = 0 then 0 else WithZero.exp (-x.valuation)) ≤ 1 ↔ ‖x‖ ≤ 1
  rw [ite_eq_right hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp, Padic.norm_eq_zpow_neg_valuation hx, zpow_le_one_iff_right₀ hq]

theorem padic_comap_mulValuation_surjective {E : Type} [Field E] [CharZero E]
    {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q]) :
    Function.Surjective ((Padic.mulValuation (p := q)).comap f) := by
  classical
  intro z
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have hq : (q : ℚ_[q]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hvq : ((Padic.mulValuation (p := q)).comap f) (q : E) = WithZero.exp (-1 : ℤ) := by
    rw [Valuation.comap_apply, map_natCast]
    change (if (q : ℚ_[q]) = 0 then 0 else WithZero.exp (-(q : ℚ_[q]).valuation)) = _
    rw [ite_eq_right hq, Padic.valuation_p]
  refine ⟨(q : E) ^ (-WithZero.log z), ?_⟩
  rw [map_zpow₀, hvq, ← WithZero.exp_zsmul]
  simpa only [smul_eq_mul, neg_mul_neg, mul_one] using WithZero.exp_log hz

theorem nativeFieldEmbedding_normalized
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (i : Fin s × Bool) :
    (Intrinsic.Primes.ParameterChoices.nativeLocalPrime D i).valuation E = (Padic.mulValuation (p := q)).comap (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i) := by
  apply discrete_valuation_eq_of_equiv
  · exact (LocalEmbedding.ParameterChoices.nativeFieldEmbedding_valuation_equiv D i).trans
      ((padic_mulValuation_equiv_norm q).comap (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i)).symm
  · exact (Intrinsic.Primes.ParameterChoices.nativeLocalPrime D i).valuation_surjective E
  · exact padic_comap_mulValuation_surjective (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i)

theorem nativeFieldEmbedding_valuation_of_value
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (i : Fin s × Bool)
    (x : E) (hx : x ≠ 0) (n : ℤ)
    (hv : (Intrinsic.Primes.ParameterChoices.nativeLocalPrime D i).valuation E x = WithZero.exp (-n)) :
    (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i x).valuation = n := by
  classical
  have hf : LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i x ≠ 0 := (map_ne_zero _).mpr hx
  have h := congrArg (fun v : Valuation E ℤᵐ⁰ => v x) (nativeFieldEmbedding_normalized D i)
  change (Intrinsic.Primes.ParameterChoices.nativeLocalPrime D i).valuation E x =
    if LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i x = 0 then 0 else WithZero.exp (-(LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i x).valuation) at h
  rw [hv, ite_eq_right hf] at h
  exact neg_injective (WithZero.exp_injective h).symm

/-- The valuation of the native norm-one scalar is now the usual additive
q-adic valuation, with its exact integer normalization. -/
theorem exists_native_scalar_normalized
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.IsGoodCompletelySplitPrime)
    (v : Fin s) (side : Bool) :
    ∃ (r : Eˣ) (M : ℕ), 0 < M ∧
      (r : E) * NumberField.IsCMField.complexConj E (r : E) = 1 ∧
      (∀ i : Fin s × Bool, (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i (r : E)).valuation =
        if i = (v, side) then (M : ℤ) else if i = (v, !side) then -(M : ℤ) else 0) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 E))) (depth : HeightOneSpectrum (𝓞 E) → ℕ),
        Intrinsic.Primes.ParameterChoices.nativeLocalPrime D (v, side) ∉ S → Intrinsic.Primes.ParameterChoices.nativeLocalPrime D (v, !side) ∉ S →
        ∃ N : ℕ, 0 < N ∧ ∀ p ∈ S,
          p.valuation E ((r : E) ^ N - 1) ≤ WithZero.exp (-(depth p : ℤ))) := by
  classical
  obtain ⟨r, M, hM, hnorm, hval, _, happrox⟩ := Intrinsic.Primes.ParameterChoices.exists_native_split_scalar D hg v side
  refine ⟨r, M, hM, hnorm, ?_, happrox⟩
  intro i
  apply nativeFieldEmbedding_valuation_of_value D i (r : E) r.ne_zero
  have h := hval i
  split_ifs at h ⊢ <;> simpa only [neg_neg, neg_zero, WithZero.exp_zero] using h

end

section

/-! The native split slots are identified with the actual Galois embeddings
using one chosen q-adic embedding and the reference datum's full embedding set. -/

open _root_.NumberField IsDedekindDomain

def embeddingAutEquiv {E F : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    [Field F] [CharZero F] (f : E →+* F) : (E →ₐ[ℚ] F) ≃ Gal(E/ℚ) := by
  let : Algebra E F := f.toAlgebra
  let : IsScalarTower ℚ E F := IsScalarTower.of_algebraMap_eq (fun r => by
    change (r : F) = f (r : E)
    simp)
  exact Normal.algHomEquivAut ℚ F E

theorem embeddingAutEquiv_spec {E F : Type} [Field E] [NumberField E] [IsGalois ℚ E]
    [Field F] [CharZero F] (f : E →+* F) (g : E →ₐ[ℚ] F) (x : E) :
    f (embeddingAutEquiv f g x) = g x := by
  exact congrArg (fun h : E →ₐ[ℚ] F => h x) ((embeddingAutEquiv f).symm_apply_apply g)

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

def nativeFieldAlgEmbedding (i : Fin s × Bool) : E →ₐ[ℚ] ℚ_[q] where
  toRingHom := LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i
  commutes' r := by simp

omit [IsGalois ℚ E] in
theorem nativeFieldAlgEmbedding_injective (hq : D.IsGoodCompletelySplitPrime) :
    Function.Injective (nativeFieldAlgEmbedding D) := by
  intro i j hij
  apply Intrinsic.Primes.ParameterChoices.nativeResidueCharacter_injective D hq
  ext a
  have h := congrArg (fun f : E →ₐ[ℚ] ℚ_[q] => f (a : E)) hij
  change LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i (a : E) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D j (a : E) at h
  rw [LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers, LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers] at h
  exact congrArg PadicInt.toZMod (PadicInt.ext h)

def nativeLocalLabel (i₀ : Fin s × Bool) (i : Fin s × Bool) : Gal(E/ℚ) :=
  embeddingAutEquiv (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i₀) (nativeFieldAlgEmbedding D i)

theorem nativeLocalLabel_spec (i₀ i : Fin s × Bool) (x : E) :
    LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i₀ (nativeLocalLabel D i₀ i x) = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i x :=
  embeddingAutEquiv_spec (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i₀) (nativeFieldAlgEmbedding D i) x

theorem nativeLocalLabel_bijective (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (i₀ : Fin s × Bool) : Function.Bijective (nativeLocalLabel D i₀) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨(embeddingAutEquiv (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i₀)).injective.comp
    (nativeFieldAlgEmbedding_injective D hq), ?_⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective _ hg.reference_admissible.1)
  exact hcard.trans (Fintype.card_congr (embeddingAutEquiv D.reference.μ))

def nativeLocalLabelEquiv (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (i₀ : Fin s × Bool) : (Fin s × Bool) ≃ Gal(E/ℚ) :=
  Equiv.ofBijective (nativeLocalLabel D i₀) (nativeLocalLabel_bijective D hg hq i₀)

theorem nativeLocalLabel_self (i₀ : Fin s × Bool) : nativeLocalLabel D i₀ i₀ = 1 := by
  ext x
  apply (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i₀).injective
  exact nativeLocalLabel_spec D i₀ i₀ x

theorem nativeFieldEmbedding_conjugate (hq : D.IsGoodCompletelySplitPrime)
    (v : Fin s) (side : Bool) :
    LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (v, !side) =
      (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (v, side)).comp (NumberField.IsCMField.complexConj E).toRingHom := by
  apply IsFractionRing.ringHom_ext (A := 𝓞 E)
  intro a
  change LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (v, !side) (a : E) =
    LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (v, side)
      (NumberField.IsCMField.ringOfIntegersComplexConj E a : E)
  rw [LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers, LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers]
  exact congrArg (fun z : ℤ_[q] => (z : ℚ_[q])) (hq.2.1 v side a)

theorem nativeLocalLabel_conjugate (hq : D.IsGoodCompletelySplitPrime)
    (v : Fin s) (side : Bool) :
    nativeLocalLabel D (v, side) (v, !side) =
      (NumberField.IsCMField.complexConj E).restrictScalars ℚ := by
  ext x
  apply (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (v, side)).injective
  exact (nativeLocalLabel_spec D (v, side) (v, !side) x).trans
    (RingHom.congr_fun (nativeFieldEmbedding_conjugate D hq v side) x)

end

/-! The actual norm-one scalar has the full Galois-labelled splitting formula,
with positive valuation at conjugation and negative valuation at identity. -/

open _root_.NumberField IsDedekindDomain
open scoped WithZero Classical

theorem exists_native_scalar_galois
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    (hq : D.IsGoodCompletelySplitPrime) (v : Fin s) (side : Bool) :
    ∃ (r : Eˣ) (M : ℕ), 0 < M ∧
      (r : E) * NumberField.IsCMField.complexConj E (r : E) = 1 ∧
      (∀ τ : Gal(E/ℚ), (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (v, side) (τ (r : E))).valuation =
        if τ = (NumberField.IsCMField.complexConj E).restrictScalars ℚ then (M : ℤ)
        else if τ = 1 then -(M : ℤ) else 0) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 E))) (depth : HeightOneSpectrum (𝓞 E) → ℕ),
        Intrinsic.Primes.ParameterChoices.nativeLocalPrime D (v, side) ∉ S → Intrinsic.Primes.ParameterChoices.nativeLocalPrime D (v, !side) ∉ S →
        ∃ N : ℕ, 0 < N ∧ ∀ p ∈ S,
          p.valuation E ((r : E) ^ N - 1) ≤ WithZero.exp (-(depth p : ℤ))) := by
  classical
  obtain ⟨r, M, hM, hnorm, hval, happrox⟩ := exists_native_scalar_normalized D hq v (!side)
  refine ⟨r, M, hM, hnorm, ?_, ?_⟩
  · intro τ
    obtain ⟨i, rfl⟩ := (nativeLocalLabel_bijective D hg hq (v, side)).2 τ
    rw [nativeLocalLabel_spec]
    have hc : nativeLocalLabel D (v, side) i =
        (NumberField.IsCMField.complexConj E).restrictScalars ℚ ↔ i = (v, !side) := by
      rw [← nativeLocalLabel_conjugate D hq v side]
      exact (nativeLocalLabel_bijective D hg hq (v, side)).1.eq_iff
    have hid : nativeLocalLabel D (v, side) i = 1 ↔ i = (v, side) := by
      rw [← nativeLocalLabel_self D (v, side)]
      exact (nativeLocalLabel_bijective D hg hq (v, side)).1.eq_iff
    simpa only [Bool.not_not, hc, hid] using hval i
  · intro S depth h₁ h₂
    exact happrox S depth h₂ (by simpa only [Bool.not_not] using h₁)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaloisDiscrete.ParameterChoices
