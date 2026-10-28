/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Christian Merten, Jingting Wang, Andrew Yang, Shouxin Zhang
This file has been modified.
-/
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! # Generator Height Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.GeneratorHeightBound

noncomputable section

open _root_.Ideal IsLocalRing
variable {R : Type*} [CommRing R] [IsNoetherianRing R]

lemma localQuotientArtinianOfMinimalPrime
    [IsLocalRing R] (I : Ideal R) (hp : IsLocalRing.maximalIdeal R ∈ I.minimalPrimes) :
    IsArtinianRing (R ⧸ I) :=
  have : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_zero_iff.mpr fun J prime ↦
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) J <| by
      convert! IsLocalRing.maximalIdeal.isMaximal R
      rw [Ideal.minimalPrimes, Set.mem_ofPred] at hp
      have := prime.comap (Ideal.Quotient.mk I)
      exact hp.eq_of_le ⟨this, .trans (by simp) (Ideal.ker_le_comap _)⟩ (le_maximalIdeal this.1)
  IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

set_option backward.isDefEq.respectTransparency.types false in
lemma localPrincipalMinimalPrimeHeight
    [IsLocalRing R] (I : Ideal R) [I.IsPrincipal]
    (hp : (IsLocalRing.maximalIdeal R) ∈ I.minimalPrimes) :
    (IsLocalRing.maximalIdeal R).height ≤ 1 := by
  refine Ideal.height_le_iff.mpr fun q h₁ h₂ ↦ ?_
  suffices q.height = 0 by rw [this]; exact zero_lt_one
  rw [← WithBot.coe_inj,
    ← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
    WithBot.coe_zero, ← ringKrullDimZero_iff_ringKrullDim_eq_zero,
    ← isArtinianRing_iff_krullDimLE_zero, isArtinianRing_iff_isNilpotent_maximalIdeal,
    ← Localization.AtPrime.map_eq_maximalIdeal]
  have : IsArtinianRing (R ⧸ I) :=
    localQuotientArtinianOfMinimalPrime I hp
  let f := algebraMap R (Localization.AtPrime q)
  let qs : ℕ →o (Ideal (R ⧸ I))ᵒᵈ :=
    { toFun n := ((q.map f ^ n).comap f).map (Ideal.Quotient.mk I)
      monotone' i j e := Ideal.map_mono (Ideal.comap_mono (Ideal.pow_le_pow_right e)) }
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes qs
  refine ⟨n, ?_⟩
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (q.map f) _ (IsNoetherian.noetherian _)
  rotate_left
  · rw [IsLocalRing.jacobson_eq_maximalIdeal, Localization.AtPrime.map_eq_maximalIdeal]
    exact bot_ne_top
  rw [smul_eq_mul, ← pow_succ',
    ← (IsLocalization.orderEmbedding q.primeCompl (Localization.AtPrime q)).map_rel_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := I) (IsNoetherian.noetherian _) ?_ ?_
  · rw [IsLocalRing.jacobson_eq_maximalIdeal]
    exacts [hp.le, bot_ne_top]
  · replace hn := congr(Ideal.comap (Ideal.Quotient.mk I) $(hn _ n.le_succ))
    simp only [qs, OrderHom.coe_mk, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at hn
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (hn.le (Ideal.mem_sup_left hx))
    refine Submodule.add_mem_sup hy ?_
    obtain ⟨z, rfl⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp hz
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
    refine Ideal.mul_mem_mul ?_ (Submodule.IsPrincipal.generator_mem _)
    dsimp [IsLocalization.orderEmbedding] at hx
    rwa [Ideal.mem_comap, f.map_add, f.map_mul, Ideal.add_mem_iff_right _
      (Ideal.pow_le_pow_right n.le_succ hy), mul_comm, Ideal.unit_mul_mem_iff_mem] at hx
    refine IsLocalization.map_units (M := q.primeCompl) _ ⟨_, ?_⟩
    change Submodule.IsPrincipal.generator I ∉ (↑q : Set R)
    rw [← Set.singleton_subset_iff, ← Ideal.span_le, Ideal.span_singleton_generator]
    exact fun e ↦ h₂.not_ge (hp.2 ⟨h₁, e⟩ h₂.le)

/-- **Krull's principal ideal theorem** (also known as **Krullscher Hauptidealsatz**):
 In a commutative Noetherian ring `R`, any prime ideal that is minimal over a principal ideal
 has height at most 1. -/
lemma principalMinimalPrimeHeight
    (I : Ideal R) [I.IsPrincipal] (p : Ideal R) (hp : p ∈ I.minimalPrimes) : p.height ≤ 1 := by
  have := hp.isPrime
  let f := algebraMap R (Localization.AtPrime p)
  have := localPrincipalMinimalPrimeHeight (I.map f) ?_
  · rwa [← IsLocalization.height_under p.primeCompl,
      Localization.AtPrime.under_maximalIdeal] at this
  · rwa [IsLocalization.minimalPrimes_map p.primeCompl (Localization.AtPrime p) I,
      Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]

theorem smallerPrimeMinimalOverReplacementGenerators {q p : Ideal R} [q.IsPrime]
    (hqp : q < p) (x : R) (s : Set R) (hp : p ∈ (span (insert x s)).minimalPrimes)
    (t : Set R) (htq : t ⊆ q) (hsp : s ⊆ (span (insert x t)).radical) :
    q ∈ (span t).minimalPrimes := by
  let f := Ideal.Quotient.mk (span t)
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hI'q : span t ≤ q := span_le.mpr htq
  have hI'p : span t ≤ p := hI'q.trans hqp.le
  have := hp.isPrime
  have : (p.map f).IsPrime := map_isPrime_of_surjective hf (by rwa [mk_ker])
  suffices h : (p.map f).height ≤ 1 by
    have h_lt : q.map f < p.map f := (map_mono hqp.le).lt_of_not_ge fun e ↦ hqp.not_ge <| by
      simpa only [comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot, f, mk_ker,
        sup_eq_left.mpr hI'q, sup_eq_left.mpr hI'p] using comap_mono (f := f) e
    have : (q.map f).IsPrime := map_isPrime_of_surjective hf (by rwa [mk_ker])
    have : (p.map f).FiniteHeight := ⟨Or.inr (h.trans_lt (WithTop.coe_lt_top 1)).ne⟩
    have := (height_strict_mono_of_isPrime_of_isPrime h_lt).trans_le h
    rw [Order.lt_one_iff, height_eq_zero_iff] at this
    have := minimalPrimes_comap_of_surjective hf this
    rwa [comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
      mk_ker, sup_eq_left.mpr hI'q] at this
  refine principalMinimalPrimeHeight ((span {x}).map f) (p.map f) ⟨⟨this,
    map_mono <| span_le.mpr <| Set.singleton_subset_iff.mpr <| hp.le <| subset_span <| .inl rfl⟩,
    fun r ⟨hr, hxr⟩ hrp ↦ map_le_iff_le_comap.mpr (hp.2 ⟨hr.comap f, ?_⟩ ?_)⟩
  · rw [span_le, Set.insert_subset_iff]
    have := map_le_iff_le_comap.mp hxr (subset_span rfl)
    refine ⟨this, hsp.trans ((hr.comap f).isRadical.radical_le_iff.mpr ?_)⟩
    rw [span_le, Set.insert_subset_iff]
    exact ⟨this, span_le.mp (mk_ker.symm.trans_le (ker_le_comap _))⟩
  · conv_rhs => rw [← sup_eq_left.mpr hI'p, ← (span t).mk_ker, RingHom.ker_eq_comap_bot,
      ← comap_map_of_surjective f hf p]
    exact comap_mono hrp

/-- **Krull's height theorem** (also known as **Krullscher Höhensatz**):
 In a commutative Noetherian ring `R`, any prime ideal that is minimal over an ideal generated
 by `n` elements has height at most `n`. -/
lemma minimalPrimeHeightLeSpanRank
    (I : Ideal R) (p : Ideal R) (hp : p ∈ I.minimalPrimes) :
    p.height ≤ I.spanRank.toENat := by
  classical
  rw [I.spanRank_toENat_eq_iInf_finset_card, le_iInf_iff]
  rintro ⟨s, (rfl : span s = I)⟩
  induction hn : s.card using Nat.strong_induction_on generalizing R with
  | h n H =>
    replace hn : s.card ≤ n := hn.le
    have := hp.isPrime
    cases n with
    | zero =>
      rw [ENat.natCast_zero, nonpos_iff_eq_zero, height_eq_zero_iff, minimalPrimes]
      simp_all
    | succ n =>
      wlog hR : ∃ (_ : IsLocalRing R), p = maximalIdeal R
      · rw [← Localization.AtPrime.under_maximalIdeal (I := p)] at hp ⊢
        rw [IsLocalization.height_under p.primeCompl]
        rw [← Set.mem_preimage, ← IsLocalization.minimalPrimes_map p.primeCompl, map_span] at hp
        exact this _ (s.image (algebraMap R (Localization p.primeCompl))) (by simpa using hp)
          inferInstance _ H (Finset.card_image_le.trans hn) ⟨inferInstance, rfl⟩
      obtain ⟨_, rfl⟩ := hR
      simp_rw [height_le_iff_covBy, ENat.natCast_add, ENat.natCast_one, ENat.lt_natCast_add_one_iff]
      intro q hq hpq hq'
      obtain ⟨x, s', hxs', rfl, hxq⟩ : ∃ x s', x ∉ s' ∧ s = insert x s' ∧ x ∉ q := by
        have : ¬(s : Set R) ⊆ q := by
          rw [← span_le]
          exact fun e ↦ lt_irrefl _ ((hp.2 ⟨hq, e⟩ hpq.le).trans_lt hpq)
        obtain ⟨x, hxt, hxq⟩ := Set.not_subset.mp this
        exact ⟨x, _, fun e ↦ (Finset.mem_erase.mp e).1 rfl, (Finset.insert_erase hxt).symm, hxq⟩
      have : maximalIdeal R ≤ (q ⊔ span {x}).radical := by
        rw [radical_eq_sInf, le_sInf_iff]
        exact fun J ⟨hJ, hJ'⟩ ↦ by_contra fun h ↦ hq' J hJ' ((SetLike.lt_iff_le_and_exists.mpr
          ⟨le_sup_left, x, mem_sup_right (mem_span_singleton_self _), hxq⟩).trans_le hJ)
          ((le_maximalIdeal hJ'.ne_top).lt_of_not_ge h)
      have h : (s' : Set R) ⊆ (q ⊔ span {x}).radical := by
        have := hp.le.trans this
        rw [span_le, Finset.coe_insert, Set.insert_subset_iff] at this
        exact this.2
      obtain ⟨t, ht, hspan⟩ := exists_subset_radical_span_sup_of_subset_radical_sup _ _ _ h
      let t := Finset.univ.image t
      suffices hq : q ∈ (span t).minimalPrimes from
        have tcard : t.card ≤ n := Nat.le_of_lt_succ ((Finset.card_image_le.trans_lt <| by
          simpa using Finset.card_lt_card (Finset.ssubset_insert hxs')).trans_le hn)
        (H _ (tcard.trans_lt n.lt_succ_self) q t hq rfl).trans (by norm_cast)
      rw [Finset.coe_insert] at hp
      convert! smallerPrimeMinimalOverReplacementGenerators hpq _ _ hp _ ht ?_
      · simp [t]
      refine hspan.trans <| radical_mono ?_
      rw [← Set.union_singleton, span_union]

lemma minimalPrimeHeightLeGeneratorCard {p : Ideal R} {s : Finset R}
    (hI : p ∈ (Ideal.span s).minimalPrimes) :
    p.height ≤ s.card := by
  trans (Cardinal.toENat (Submodule.spanRank (Ideal.span (s : Set R))))
  · exact minimalPrimeHeightLeSpanRank _ _ hI
  · simpa using Submodule.spanRank_span_le_card (s : Set R)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.GeneratorHeightBound
