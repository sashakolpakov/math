import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicData
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-! # Adelic Neighborhoods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicNeighborhoods

noncomputable section

section

/-! A nonzero integer multiple of the local integer ring fits inside
any zero-neighborhood in each finite completion. This is the local
step in the finite-adelic principal-congruence neighborhood argument. -/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped _root_.Topology

theorem adic_integer_multiple_small (v : HeightOneSpectrum ℤ)
    (U : Set (v.adicCompletion ℚ)) (hU : U ∈ 𝓝 (0 : v.adicCompletion ℚ)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ a ∈ v.adicCompletionIntegers ℚ,
      algebraMap ℤ (v.adicCompletion ℚ) n * a ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  obtain ⟨ϖ, hϖ⟩ := intValuation_exists_uniformizer v
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact (WithZero.exp_ne_zero : WithZero.exp (-1 : ℤ) ≠ 0) hϖ.symm
  have hval : Valued.v (algebraMap ℤ (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ) := by
    simpa only [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap] using hϖ
  have hlt : Valued.v (algebraMap ℤ (v.adicCompletion ℚ) ϖ) < 1 := by
    rw [hval, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hlt
  have hball : {x : v.adicCompletion ℚ | Valued.v.restrict x < γ} ∈ 𝓝 (0 : v.adicCompletion ℚ) :=
    Valued.mem_nhds_zero.mpr ⟨γ, Set.Subset.rfl⟩
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp (ht hball)
  refine ⟨ϖ ^ r, pow_ne_zero r hϖ0, ?_⟩
  intro a ha
  have ha' : Valued.v.restrict a ≤ 1 := (Valued.v.restrict_le_one_iff).mpr
    ((mem_adicCompletionIntegers ℤ ℚ v).mp ha)
  apply hγ
  change Valued.v.restrict (algebraMap ℤ (v.adicCompletion ℚ) (ϖ ^ r) * a) < γ
  rw [map_mul, map_pow]
  exact (calc
    Valued.v.restrict ((algebraMap ℤ (v.adicCompletion ℚ) ϖ) ^ r) * Valued.v.restrict a ≤
        Valued.v.restrict ((algebraMap ℤ (v.adicCompletion ℚ) ϖ) ^ r) * 1 := mul_le_mul_right ha' _
    _ = _ := mul_one _).trans_lt (hr r le_rfl)

end

/-! Nonzero integer multiples of the integral finite adeles form a
basis of zero-neighborhoods inside the rational finite adele ring. The
proof combines finitely many local valuation bounds in the product of
local integer rings. -/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical _root_.Topology

abbrev IntegralAdeleProduct := ∀ v : HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ

def integralAdeleProductMap : IntegralAdeleProduct → AdelicData.RationalFiniteAdeles :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) Filter.cofinite

theorem integralAdeleProductMap_continuous : Continuous integralAdeleProductMap :=
  RestrictedProduct.isEmbedding_structureMap.continuous

theorem integralAdeleProductMap_zero : integralAdeleProductMap 0 = 0 := rfl

theorem local_integer_multiple_small (v : HeightOneSpectrum ℤ)
    (W : Set (v.adicCompletionIntegers ℚ)) (hW : W ∈ 𝓝 (0 : v.adicCompletionIntegers ℚ)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ a : v.adicCompletionIntegers ℚ, n • a ∈ W := by
  rw [nhds_subtype_eq_comap] at hW
  obtain ⟨U, hU, hUW⟩ := Filter.mem_comap.mp hW
  obtain ⟨n, hn, hsmall⟩ := adic_integer_multiple_small v U hU
  refine ⟨n, hn, fun a => hUW ?_⟩
  change ((n • a : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ∈ U
  have h := hsmall a.val a.property
  have hcoe : ((n • a : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = n • a.val :=
    map_zsmul (v.adicCompletionIntegers ℚ).toSubring.subtype n a
  rw [hcoe, zsmul_eq_mul]
  rw [← map_intCast (algebraMap ℤ (v.adicCompletion ℚ)) n]
  exact h

theorem finite_adele_integer_multiple_small
    (U : Set AdelicData.RationalFiniteAdeles) (hU : U ∈ 𝓝 (0 : AdelicData.RationalFiniteAdeles)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ a ∈ AdelicData.integralFiniteAdeles, n • a ∈ U := by
  have hpre : integralAdeleProductMap ⁻¹' U ∈ 𝓝 (0 : IntegralAdeleProduct) :=
    integralAdeleProductMap_continuous.continuousAt.preimage_mem_nhds hU
  rw [nhds_pi] at hpre
  obtain ⟨I, W, hW, hsub⟩ := Filter.mem_pi'.mp hpre
  choose n hn hsmall using fun v => local_integer_multiple_small v (W v) (hW v)
  refine ⟨∏ v ∈ I, n v, Finset.prod_ne_zero_iff.mpr (fun v _ => hn v), ?_⟩
  intro a ha
  let b : IntegralAdeleProduct := fun v => ⟨a v, ha v⟩
  have hb : (∏ v ∈ I, n v) • b ∈ Set.pi (I : Set (HeightOneSpectrum ℤ)) W := by
    intro v hv
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n hv
    change (∏ v ∈ I, n v) • b v ∈ W v
    rw [hc, mul_smul]
    exact hsmall v (c • b v)
  have hmem := hsub hb
  have he : integralAdeleProductMap ((∏ v ∈ I, n v) • b) = (∏ v ∈ I, n v) • a := by
    apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    rfl
  exact he ▸ hmem

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicNeighborhoods
