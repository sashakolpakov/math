import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! # Dedekind Approximation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DedekindApproximation

noncomputable section

/-! Finite weak approximation for the actual height-one valuations of a
Dedekind domain. Chinese remainders prescribe arbitrary orders at a finite
family of distinct prime ideals. -/

open IsDedekindDomain WithZero

universe u v

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

theorem exists_integral_orders {ι : Type v} [Fintype ι]
    (v : ι → HeightOneSpectrum R) (hv : Function.Injective v) (e : ι → ℕ) :
    ∃ r : R, r ≠ 0 ∧ ∀ i, (v i).intValuation r = exp (-(e i : ℤ)) := by
  classical
  by_cases hι : Nonempty ι
  · choose π hπ using fun i => (v i).intValuation_exists_uniformizer
    have ht (i : ι) : (v i).intValuation (π i ^ e i) = exp (-(e i : ℤ)) := by
      rw [map_pow, hπ, ← WithZero.exp_nsmul]
      simp
    obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal
      (I := fun i => (v i).asIdeal ^ (e i + 1))
      (fun i j hij => (v i).isCoprime_pow_of_ne (v j) (hv.ne hij) _ _) (fun i => π i ^ e i)
    have he (i : ι) : (v i).intValuation r = exp (-(e i : ℤ)) := by
      rw [← ht i]
      apply Valuation.map_eq_of_sub_lt
      apply ((v i).intValuation_le_pow_iff_mem _ (e i + 1)).mpr (hr i) |>.trans_lt
      rw [ht i, WithZero.exp_lt_exp]
      omega
    refine ⟨r, ?_, he⟩
    intro hz
    have h := he (Classical.choice hι)
    rw [hz, map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  · let : IsEmpty ι := not_nonempty_iff.mp hι
    exact ⟨1, one_ne_zero, fun i => isEmptyElim i⟩

theorem exists_fractional_orders (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {ι : Type v} [Fintype ι] (v : ι → HeightOneSpectrum R) (hv : Function.Injective v)
    (e : ι → ℤ) : ∃ r : K, r ≠ 0 ∧ ∀ i, (v i).valuation K r = exp (-e i) := by
  obtain ⟨a, ha, hea⟩ := exists_integral_orders R v hv (fun i => (e i).toNat)
  obtain ⟨b, hb, heb⟩ := exists_integral_orders R v hv (fun i => (-e i).toNat)
  refine ⟨algebraMap R K a / algebraMap R K b, div_ne_zero ?_ ?_, ?_⟩
  · simpa only [map_zero] using (IsFractionRing.injective R K).ne ha
  · simpa only [map_zero] using (IsFractionRing.injective R K).ne hb
  · intro i
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, hea, heb, ← WithZero.exp_sub]
    congr 1
    omega

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DedekindApproximation
