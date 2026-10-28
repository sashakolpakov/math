import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-! # Normal Local Denominator -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalLocalDenominator

noncomputable section

/-! In a normal local domain, a fraction outside the ring whose product with
the maximal ideal lies in the ring forces that maximal ideal to be principal.
This isolates the determinant-trick step in the local DVR argument. -/

open IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsLocalRing R] [IsIntegrallyClosed R]

theorem maximal_principal (a b : R) (ha : a ≠ 0) (hb : b ∉ Ideal.span {a})
    (hm : ∀ m ∈ maximalIdeal R, ∃ k : R, k * a = b * m) :
    (maximalIdeal R).IsPrincipal := by
  have ha₁ : a ∈ maximalIdeal R := by
    by_contra h
    have hu : IsUnit a := (notMem_maximalIdeal).mp h
    apply hb
    rw [Ideal.span_singleton_eq_top.mpr hu]
    trivial
  have hb₀ : b ≠ 0 := by
    rintro rfl
    exact hb (Submodule.zero_mem _)
  let K := FractionRing R
  let x : K := algebraMap R K b / algebraMap R K a
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have haK : algebraMap R K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha
  by_cases hx : ∀ y ∈ M, x * y ∈ M
  · have hi := isIntegral_of_smul_mem_submodule M ?_ ?_ x hx
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
      refine (hb (Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩)).elim
      apply IsFractionRing.injective R K
      rw [map_mul, e, div_mul_cancel₀ _ haK]
    · rw [Submodule.ne_bot_iff]
      exact ⟨_, ⟨a, ha₁, rfl⟩, haK⟩
    · exact (IsNoetherian.noetherian _).map _
  · have htop :
        (M.map (DistribSMul.toLinearMap R K x)).comap (Algebra.linearMap R K) = ⊤ := by
      contrapose! hx with h
      rintro m' ⟨m, hm', rfl : algebraMap R K m = m'⟩
      obtain ⟨k, hk⟩ := hm m hm'
      have hk' : x * algebraMap R K m = algebraMap R K k := by
        rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel_right₀ _ haK]
      exact ⟨k, le_maximalIdeal h ⟨_, ⟨_, hm', rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨y, hy, hby⟩ : ∃ y ∈ maximalIdeal R, b * y = a := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at htop
      obtain ⟨_, ⟨y, hy, rfl⟩, hy' : x * algebraMap R K y = algebraMap R K 1⟩ := htop
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq haK, ← map_mul] at hy'
      exact ⟨y, hy, IsFractionRing.injective R K hy'⟩
    refine ⟨⟨y, le_antisymm ?_ ?_⟩⟩
    · intro m hm'
      obtain ⟨k, hk⟩ := hm m hm'
      rw [← hby, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ hb₀ hk, mul_comm]
      exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hy)

theorem maximal_associated_principal (a : R) (ha : a ≠ 0)
    (h : IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.span {a})) :
    (maximalIdeal R).IsPrincipal := by
  obtain ⟨_, x, hx⟩ := isAssociatedPrime_iff.mp h
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply maximal_principal R a b ha
  · intro hb
    have hx₀ : Ideal.Quotient.mk (Ideal.span {a}) b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    have he : maximalIdeal R = ⊤ := by
      simpa only [hx₀, Submodule.colon_singleton_zero] using hx
    exact (maximalIdeal.isMaximal R).ne_top he
  · intro m hm
    have hz : m • Ideal.Quotient.mk (Ideal.span {a}) b = 0 := by
      have hz := Submodule.mem_colon_singleton.mp (hx ▸ hm)
      exact hz
    have hmb : m * b ∈ Ideal.span {a} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change Ideal.Quotient.mk (Ideal.span {a}) (m * b) = 0
      exact hz
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hmb
    exact ⟨k, hk.trans (mul_comm m b)⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalLocalDenominator
