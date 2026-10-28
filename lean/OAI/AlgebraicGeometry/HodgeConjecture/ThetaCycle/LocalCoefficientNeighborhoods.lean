import OAI.RepresentationTheory.Weil.AdelicSplitting.Integral
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt

/-! # Local Coefficient Neighborhoods -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalCoefficientNeighborhoods.CM

noncomputable section

section

/-! ThetaCycle: rational integer powers make the actual local integer lattice
uniformly small at every finite place of the maximal real field. -/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped _root_.NumberField _root_.Topology

theorem number_field_adic_integer_multiple_small (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (U : Set (v.adicCompletion F)) (hU : U ∈ 𝓝 (0 : v.adicCompletion F)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ a ∈ v.adicCompletionIntegers F,
      algebraMap ℤ (v.adicCompletion F) n * a ∈ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  let p : ℤ := Ideal.absNorm v.asIdeal
  have hp : p ≠ 0 := Int.natCast_ne_zero.mpr
    (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  have hval : Valued.v (algebraMap ℤ (v.adicCompletion F) p) < 1 := by
    have he := valuedAdicCompletion_eq_valuation (K := F) v (p : 𝓞 F)
    rw [valuation_of_algebraMap] at he
    have hs : v.intValuation (p : 𝓞 F) < 1 := (intValuation_lt_one_iff_mem v (p : 𝓞 F)).mpr (by
      simpa only [p, Int.cast_natCast] using Ideal.absNorm_mem v.asIdeal)
    simpa [p] using! he.trans_lt hs
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hval
  have hball : {x : v.adicCompletion F | Valued.v.restrict x < γ} ∈ 𝓝 (0 : v.adicCompletion F) :=
    Valued.mem_nhds_zero.mpr ⟨γ, Set.Subset.rfl⟩
  obtain ⟨r, hr⟩ := Filter.eventually_atTop.mp (ht hball)
  refine ⟨p ^ r, pow_ne_zero r hp, ?_⟩
  intro a ha
  have ha' : Valued.v.restrict a ≤ 1 := (Valued.v.restrict_le_one_iff).mpr
    ((mem_adicCompletionIntegers (𝓞 F) F v).mp ha)
  apply hγ
  change Valued.v.restrict (algebraMap ℤ (v.adicCompletion F) (p ^ r) * a) < γ
  rw [map_mul, map_pow]
  exact (calc
    Valued.v.restrict ((algebraMap ℤ (v.adicCompletion F) p) ^ r) * Valued.v.restrict a ≤
        Valued.v.restrict ((algebraMap ℤ (v.adicCompletion F) p) ^ r) * 1 := mul_le_mul_right ha' _
    _ = _ := mul_one _).trans_lt (hr r le_rfl)

end

/-! ThetaCycle: one rational integer controls a finite tuple of local integral
coefficients in any prescribed zero-neighborhood. -/

open IsDedekindDomain
open scoped Classical _root_.NumberField _root_.Topology

theorem local_integral_tuple_integer_multiple_small (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {I : Type*} [Fintype I]
    (U : Set (I → v.adicCompletion F)) (hU : U ∈ 𝓝 (0 : I → v.adicCompletion F)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ a : I → v.adicCompletion F,
      (∀ i, a i ∈ v.adicCompletionIntegers F) →
        (fun i => algebraMap ℤ (v.adicCompletion F) n * a i) ∈ U := by
  rw [nhds_pi] at hU
  obtain ⟨J, W, hW, hsub⟩ := Filter.mem_pi'.mp hU
  choose n hn hs using fun i => number_field_adic_integer_multiple_small F v (W i) (hW i)
  refine ⟨∏ i, n i, Finset.prod_ne_zero_iff.mpr (fun i _ => hn i), ?_⟩
  intro a ha
  apply hsub
  intro i _
  change algebraMap ℤ (v.adicCompletion F) (∏ i, n i) * a i ∈ W i
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, map_mul, mul_assoc]
  apply hs i
  have hm := (v.adicCompletionIntegers F).toSubring.mul_mem
    (intCast_mem (v.adicCompletionIntegers F) c) (ha i)
  rw [show algebraMap ℤ (v.adicCompletion F) c = (c : v.adicCompletion F) from
    map_intCast (algebraMap ℤ (v.adicCompletion F)) c]
  exact hm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalCoefficientNeighborhoods.CM
