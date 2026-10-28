import Mathlib

/-! # Differential Derivation Core -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialDerivationCore.Construction

noncomputable section

section

/-! In characteristic zero, an ideal preserved by a derivation has a
radical preserved by the same derivation. This is the algebraic step
needed to pass infinitesimal invariance to a reduced closed subgroup. -/

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

theorem derivation_pow_mul_self (D : Derivation k A A) (x : A) (n : ℕ) :
    D (x ^ n) * x = n • (x ^ n * D x) := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Derivation.leibniz_pow]
      simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, pow_succ]
      ring

theorem derivation_power_step_identity (D : Derivation k A A) (x : A) (a b : ℕ) :
    D (x ^ (a + 1) * (D x) ^ b) * D x =
      (a + 1) • (x ^ a * (D x) ^ (b + 2)) +
        b • (x ^ (a + 1) * (D x) ^ b * D (D x)) := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul, add_mul]
  rw [mul_assoc (x ^ (a + 1)), derivation_pow_mul_self,
    Derivation.leibniz_pow]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, pow_add, pow_one, pow_two]
  ring

variable [CharZero k]

theorem derivation_power_mem (D : Derivation k A A) (I : Ideal A)
    (hD : ∀ x ∈ I, D x ∈ I) (x : A) (a b : ℕ)
    (h : x ^ a * (D x) ^ b ∈ I) : (D x) ^ (b + 2 * a) ∈ I := by
  induction a generalizing b with
  | zero => simpa using h
  | succ a ih =>
      have hfirst : D (x ^ (a + 1) * (D x) ^ b) * D x ∈ I :=
        I.mul_mem_right _ (hD _ h)
      have hsecond : b • (x ^ (a + 1) * (D x) ^ b * D (D x)) ∈ I :=
        I.nsmul_mem (I.mul_mem_right _ h) b
      rw [derivation_power_step_identity] at hfirst
      have hscale : (a + 1) • (x ^ a * (D x) ^ (b + 2)) ∈ I :=
        (I.add_mem_iff_left hsecond).mp hfirst
      have hscale' : ((a + 1 : ℕ) : k) • (x ^ a * (D x) ^ (b + 2)) ∈ I := by
        simpa only [Nat.cast_smul_eq_nsmul] using hscale
      have ha : ((a + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero a)
      have hnext : x ^ a * (D x) ^ (b + 2) ∈ I :=
        ((I.restrictScalars k).smul_mem_iff ha).mp hscale'
      have hh := ih (b + 2) hnext
      have he : b + 2 * a.succ = b + 2 + 2 * a := by omega
      rw [he]
      exact hh

theorem derivation_preserves_radical (D : Derivation k A A) (I : Ideal A)
    (hD : ∀ x ∈ I, D x ∈ I) : ∀ x ∈ I.radical, D x ∈ I.radical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have h : x ^ n * (D x) ^ 0 ∈ I := by simpa using hn
  exact ⟨2 * n, by simpa using derivation_power_mem D I hD x n 0 h⟩

end

section

/-! The largest ideal inside a given ideal preserved by a specified
family of derivations. Over characteristic zero, the core of a radical
ideal is radical. -/

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

def derivativeIdealStep (S : Set (Derivation k A A)) (I : Ideal A) : Ideal A where
  carrier := {x | x ∈ I ∧ ∀ D ∈ S, D x ∈ I}
  zero_mem' := ⟨I.zero_mem, by intro D _; simp⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨I.add_mem hx hy, ?_⟩
    intro D hD
    rw [map_add]
    exact I.add_mem (hx' D hD) (hy' D hD)
  smul_mem' := by
    rintro a x ⟨hx, hx'⟩
    refine ⟨I.smul_mem a hx, ?_⟩
    intro D hD
    change D (a * x) ∈ I
    rw [Derivation.leibniz]
    exact I.add_mem (I.smul_mem a (hx' D hD)) (I.mul_mem_right _ hx)

def iteratedDerivativeIdeal (S : Set (Derivation k A A)) (I : Ideal A) : ℕ → Ideal A
  | 0 => I
  | n + 1 => derivativeIdealStep S (iteratedDerivativeIdeal S I n)

def differentialCore (S : Set (Derivation k A A)) (I : Ideal A) : Ideal A :=
  ⨅ n, Construction.iteratedDerivativeIdeal S I n

theorem differentialCore_le (S : Set (Derivation k A A)) (I : Ideal A) :
    differentialCore S I ≤ I := iInf_le _ 0

theorem differentialCore_derivation (S : Set (Derivation k A A)) (I : Ideal A)
    (D : Derivation k A A) (hD : D ∈ S) {x : A} (hx : x ∈ differentialCore S I) :
    D x ∈ differentialCore S I := by
  apply Ideal.mem_iInf.mpr
  intro n
  have hn := Ideal.mem_iInf.mp hx (n + 1)
  exact hn.2 D hD

theorem le_differentialCore (S : Set (Derivation k A A)) (I J : Ideal A)
    (hle : J ≤ I) (hD : ∀ D ∈ S, ∀ x ∈ J, D x ∈ J) : J ≤ differentialCore S I := by
  apply le_iInf
  intro n
  induction n with
  | zero => exact hle
  | succ n ih =>
      intro x hx
      exact ⟨ih hx, fun D hDS => ih (hD D hDS x hx)⟩

theorem differentialCore_isRadical [CharZero k]
    (S : Set (Derivation k A A)) (I : Ideal A) (hI : I.IsRadical) :
    (differentialCore S I).IsRadical := by
  change (differentialCore S I).radical ≤ differentialCore S I
  apply le_differentialCore
  · exact hI.radical_le_iff.mpr (differentialCore_le S I)
  · intro D hD
    exact derivation_preserves_radical D _ (fun _ hx => differentialCore_derivation S I D hD hx)

end

/-! Polynomial maps intertwining a family of derivations preserve its
differential core when they preserve the initial ideal. -/

theorem differentialCore_map_mem
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (S : Set (Derivation k A A)) (I : Ideal A) (f : A →ₐ[k] A)
    (hf : ∀ x ∈ I, f x ∈ I)
    (hcomm : ∀ D ∈ S, ∃ E ∈ S, ∀ x, D (f x) = f (E x))
    {x : A} (hx : x ∈ differentialCore S I) : f x ∈ differentialCore S I := by
  apply Ideal.mem_iInf.mpr
  intro n
  induction n generalizing x with
  | zero => exact hf x (differentialCore_le S I hx)
  | succ n ih =>
      refine ⟨ih hx, ?_⟩
      intro D hD
      obtain ⟨E, hE, he⟩ := hcomm D hD
      rw [he]
      exact ih (differentialCore_derivation S I E hE hx)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialDerivationCore.Construction
