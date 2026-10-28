import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialDerivationCore
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! # Differential Prime -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.DifferentialPrime

noncomputable section

/-! The differential core of a prime ideal in characteristic zero is
prime. Minimal primes over a radical differential ideal are preserved by
its derivations. This will prove irreducibility of the algebraic hull. -/

theorem minimalPrime_mul_mem_radical_ideal
    {A : Type*} [CommRing A] {I P : Ideal A} (hI : I.IsRadical)
    (hP : I.IsMinimalPrime P) {x : A} (hx : x ∈ P) :
    ∃ y ∉ P, x * y ∈ I := by
  let : P.IsPrime := hP.isPrime
  have hle : P.map (algebraMap A (Localization.AtPrime P)) ≤
      (I.map (algebraMap A (Localization.AtPrime P))).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro Q ⟨hIQ, hQ⟩
    obtain ⟨hprime, hQP⟩ :=
      ((IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime P) P) ⟨Q, hQ⟩).2
    rw [Ideal.map_le_iff_le_comap] at hIQ ⊢
    exact hP.2 ⟨hprime, hIQ⟩ hQP
  obtain ⟨m, hm⟩ := hle (Ideal.mem_map_of_mem _ hx)
  rw [IsLocalization.mem_map_algebraMap_iff (M := P.primeCompl)] at hm
  obtain ⟨⟨a, b⟩, hm⟩ := hm
  rw [← map_pow, ← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hm
  obtain ⟨t, ht⟩ := hm
  refine ⟨t.val * b.val, (t * b).property, ?_⟩
  apply hI
  refine ⟨m + 1, ?_⟩
  have he : (x * (t.val * b.val)) ^ (m + 1) =
      (t.val ^ m * b.val ^ m * x * t.val) * a.val := by
    rw [mul_assoc, ← ht]
    ring
  rw [he]
  exact I.mul_mem_left _ a.property

theorem derivation_preserves_minimalPrime
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (D : Derivation k A A) {I P : Ideal A} (hI : I.IsRadical)
    (hD : ∀ x ∈ I, D x ∈ I) (hP : I.IsMinimalPrime P) {x : A} (hx : x ∈ P) :
    D x ∈ P := by
  obtain ⟨y, hy, hxy⟩ := minimalPrime_mul_mem_radical_ideal hI hP hx
  have hsum : x * D y + y * D x ∈ P := by
    simpa only [Derivation.leibniz, smul_eq_mul] using hP.le (hD (x * y) hxy)
  have hm := P.sub_mem hsum (P.mul_mem_right (D y) hx)
  rw [add_sub_cancel_left] at hm
  exact (hP.isPrime.mem_or_mem hm).resolve_left hy

theorem differentialCore_isPrime
    {k A : Type*} [Field k] [CharZero k] [CommRing A] [Algebra k A]
    (S : Set (Derivation k A A)) (P : Ideal A) [P.IsPrime] :
    (ArithmeticGroups.Lattices.DifferentialDerivationCore.Construction.differentialCore S P).IsPrime := by
  let C := ArithmeticGroups.Lattices.DifferentialDerivationCore.Construction.differentialCore S P
  have hC : C.IsRadical := ArithmeticGroups.Lattices.DifferentialDerivationCore.Construction.differentialCore_isRadical S P
    (inferInstance : P.IsPrime).isRadical
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le
    (ArithmeticGroups.Lattices.DifferentialDerivationCore.Construction.differentialCore_le S P)
  have hQC : Q ≤ C := by
    apply ArithmeticGroups.Lattices.DifferentialDerivationCore.Construction.le_differentialCore S P Q hQP
    intro D hD x hx
    exact derivation_preserves_minimalPrime D hC
      (fun _ hz => ArithmeticGroups.Lattices.DifferentialDerivationCore.Construction.differentialCore_derivation S P D hD hz) hQ hx
  have he : C = Q := le_antisymm hQ.le hQC
  change C.IsPrime
  rw [he]
  exact hQ.isPrime

end

end OAI.NumberTheory.Quaternion.Arithmetic.DifferentialPrime
