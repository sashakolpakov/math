import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedTorEuler
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-! # Prime Filtration Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler

noncomputable section

/-! A prime filtration computes the native Tor Euler characteristic as
the finite sum of the contributions of its prime quotient factors. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R]

theorem euler_iso_left {M M' : ModuleCat.{u} R} (e : M ≅ M') (N : ModuleCat R) (d : ℕ) :
    ProjectionFormula.Tor.Euler.euler R M N d = ProjectionFormula.Tor.Euler.euler R M' N d := by
  apply Finset.sum_congr rfl
  intro i _
  have h := (((Tor (ModuleCat R) i).flip.obj N).mapIso e).toLinearEquiv.length_eq
  exact congrArg (fun a : ℕ∞ => (-1 : ℚ) ^ i * (a.toNat : ℚ)) h

theorem euler_zero_left (M N : ModuleCat.{u} R) [Subsingleton M] (d : ℕ) :
    ProjectionFormula.Tor.Euler.euler R M N d = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  let := ProjectionFormula.Tor.Support.subsingleton_left R M N i
  simp [ExactLength.rationalLength, Module.length_eq_zero]

theorem euler_unit_right (M : ModuleCat.{u} R) (d : ℕ) :
    ProjectionFormula.Tor.Euler.euler R M (.of R R) d = ExactLength.rationalLength R M := by
  rw [ProjectionFormula.Tor.Euler.euler, Finset.sum_range_succ']
  have hz (n : ℕ) : ExactLength.rationalLength R
      (((Tor (ModuleCat R) (n + 1)).obj M).obj (.of R R)) = 0 := by
    let := ModuleCat.subsingleton_of_isZero
      (isZero_Tor_succ_of_projective (ModuleCat R) M (.of R R) n)
    simp [ExactLength.rationalLength, Module.length_eq_zero]
  simp only [hz, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, one_mul]
  unfold ExactLength.rationalLength
  rw [ProjectionFormula.Tor.Flat.torZero_length]
  exact congrArg (fun a : ℕ∞ => (a.toNat : ℚ)) (TensorProduct.rid R M).length_eq

variable [IsNoetherianRing R]

theorem submodule_step (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (d : ℕ) [HasProjectiveDimensionLE N d] (p : PrimeSpectrum R)
    (hp : Module.support R M ∩ Module.support R N ⊆ {p})
    (L K : Submodule R M) (hLK : L ≤ K) :
    ProjectionFormula.Tor.Euler.euler R (.of R K) N d = ProjectionFormula.Tor.Euler.euler R (.of R L) N d +
      ProjectionFormula.Tor.Euler.euler R (.of R (K ⧸ L.submoduleOf K)) N d := by
  let S := IsolatedTorEuler.submoduleSequence R (.of R K) (L.submoduleOf K)
  let : Module.Finite R S.X₂ := (inferInstance : Module.Finite R K)
  have hK : Module.support R K ∩ Module.support R N ⊆ {p} :=
    (Set.inter_subset_inter_left _
      (Module.support_subset_of_injective K.subtype K.subtype_injective)).trans hp
  have h := IsolatedTorEuler.additivity R N S
    (IsolatedTorEuler.submoduleSequence_shortExact R (.of R K) (L.submoduleOf K)) d p hK
  change ProjectionFormula.Tor.Euler.euler R (.of R K) N d =
    ProjectionFormula.Tor.Euler.euler R (.of R (L.submoduleOf K)) N d +
      ProjectionFormula.Tor.Euler.euler R (.of R (K ⧸ L.submoduleOf K)) N d at h
  rw [euler_iso_left R (Submodule.submoduleOfEquivOfLe hLK).toModuleIso N d] at h
  exact h

theorem filtration_sum (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (d : ℕ) [HasProjectiveDimensionLE N d] (p : PrimeSpectrum R)
    (hp : Module.support R M ∩ Module.support R N ⊆ {p})
    (s : RelSeries {(L, K) | Submodule.IsQuotientEquivQuotientPrime (A := R) (M := M) L K})
    (h₀ : s.head = ⊥) (ht : s.last = ⊤) :
    ProjectionFormula.Tor.Euler.euler R M N d =
      ∑ i : Fin s.length, ProjectionFormula.Tor.Euler.euler R
        (.of R (s i.succ ⧸ (s i.castSucc).submoduleOf (s i.succ))) N d := by
  have hs (n : ℕ) (hn : n < s.length + 1) :
      ProjectionFormula.Tor.Euler.euler R (.of R (s ⟨n, hn⟩)) N d =
        ∑ i : Fin n, ProjectionFormula.Tor.Euler.euler R
          (.of R (s ⟨i.val + 1, (Nat.succ_le_of_lt i.isLt).trans_lt hn⟩ ⧸
            (s ⟨i.val, i.isLt.trans hn⟩).submoduleOf
              (s ⟨i.val + 1, (Nat.succ_le_of_lt i.isLt).trans_lt hn⟩))) N d := by
    induction n with
    | zero =>
      change ProjectionFormula.Tor.Euler.euler R (.of R s.head) N d = _
      rw [h₀, euler_zero_left]
      simp
    | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      rw [submodule_step R M N d p hp (s ⟨n, by omega⟩) (s ⟨n + 1, hn⟩)
        (s.step ⟨n, by omega⟩).1, ih (by omega)]
      rfl
  have h := hs s.length (by omega)
  change ProjectionFormula.Tor.Euler.euler R (.of R s.last) N d = _ at h
  rw [ht, euler_iso_left R (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M).toModuleIso N d] at h
  exact h

theorem exists_prime_sum (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (d : ℕ) [HasProjectiveDimensionLE N d] (p : PrimeSpectrum R)
    (hp : Module.support R M ∩ Module.support R N ⊆ {p}) :
    ∃ (n : ℕ) (primes : Fin n → PrimeSpectrum R),
      (∀ i, Module.support R (R ⧸ (primes i).asIdeal) ⊆ Module.support R M) ∧
      ProjectionFormula.Tor.Euler.euler R M N d =
        ∑ i : Fin n, ProjectionFormula.Tor.Euler.euler R (.of R (R ⧸ (primes i).asIdeal)) N d := by
  obtain ⟨s, h₀, ht⟩ := IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime R M
  choose primes e using fun i => (s.step i).2
  refine ⟨s.length, primes, ?_, ?_⟩
  · intro i
    have h₁ := Module.support_subset_of_surjective
      ((s i.castSucc).submoduleOf (s i.succ)).mkQ (Submodule.mkQ_surjective _)
    have h₂ := Module.support_subset_of_injective (s i.succ).subtype
      (Submodule.subtype_injective _)
    rw [← (e i).some.support_eq]
    exact h₁.trans h₂
  · rw [filtration_sum R M N d p hp s h₀ ht]
    apply Finset.sum_congr rfl
    intro i _
    exact euler_iso_left R (e i).some.toModuleIso N d

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler
