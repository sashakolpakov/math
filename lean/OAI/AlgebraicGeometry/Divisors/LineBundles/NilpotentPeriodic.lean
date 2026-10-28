import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.FactorEuler
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Exact

/-! # Nilpotent Periodic -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.NilpotentPeriodic.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: equality of scalar presentations and the unit endpoint
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem equationPeriodicHomology_length_congr (a b a' b' : R) (ha : a = a') (hb : b = b')
    (h : ∀ m : M, (a * b) • m = 0) (h' : ∀ m : M, (a' * b') • m = 0) (i : Bool) :
    Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b h).homology i) =
      Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a' b' h').homology i) := by
  subst a'
  subst b'
  rfl

theorem equationPeriodicEulerLength_congr (a b a' b' : R) (ha : a = a') (hb : b = b')
    (h : ∀ m : M, (a * b) • m = 0) (h' : ∀ m : M, (a' * b') • m = 0)
    (h₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b h).homology false) ≠ ⊤)
    (h₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b h).homology true) ≠ ⊤)
    (h₀' : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a' b' h').homology false) ≠ ⊤)
    (h₁' : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a' b' h').homology true) ≠ ⊤) :
    Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a b h) h₀ h₁ =
      Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a' b' h') h₀' h₁' := by
  subst a'
  subst b'
  rfl

theorem equationPeriodic_one_right_exact (a : R) (h : ∀ m : M, (a * 1) • m = 0) :
    Function.Exact (MultiplicationSequence.BundleCycles.equationEndomorphism a M) (MultiplicationSequence.BundleCycles.equationEndomorphism (1 : R) M) := by
  intro m
  change (1 : R) • m = 0 ↔ ∃ x : M, a • x = m
  rw [one_smul]
  constructor
  · intro hm
    exact ⟨0, (smul_zero a).trans hm.symm⟩
  · rintro ⟨x, rfl⟩
    simpa only [mul_one] using h x

theorem equationPeriodic_one_left_exact (a : R) (h : ∀ m : M, (a * 1) • m = 0) :
    Function.Exact (MultiplicationSequence.BundleCycles.equationEndomorphism (1 : R) M) (MultiplicationSequence.BundleCycles.equationEndomorphism a M) := by
  intro m
  change a • m = 0 ↔ ∃ x : M, (1 : R) • x = m
  constructor
  · intro _
    exact ⟨m, one_smul R m⟩
  · intro _
    simpa only [mul_one] using h m

theorem equationPeriodicEulerLength_one_right (a : R) (h : ∀ m : M, (a * 1) • m = 0)
    (h₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a 1 h).homology false) ≠ ⊤)
    (h₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a 1 h).homology true) ≠ ⊤) :
    Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a 1 h) h₀ h₁ = 0 :=
  Periodic.Exact.BundleCycles.endomorphismPeriodicEulerLength_zero_of_exact _ _ _ _
    (equationPeriodic_one_right_exact a h) (equationPeriodic_one_left_exact a h) h₀ h₁

end

section

/-!
# LineBundleCycles: periodic complexes for complementary powers of a nilpotent scalar

The exponent parameter records every complementary pair. Finiteness
is imposed on the actual homology modules, independently of the Euler
identities that will be derived from factor composition.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem powerPeriodic_kill (x : R) (n : ℕ) (h : ∀ m : M, x ^ n • m = 0)
    (i : ℕ) (hi : i ≤ n) : ∀ m : M, (x ^ i * x ^ (n - i)) • m = 0 := by
  intro m
  rw [← pow_add, Nat.add_sub_of_le hi]
  exact h m

def powerPeriodicComplex (x : R) (n : ℕ) (h : ∀ m : M, x ^ n • m = 0)
    (i : ℕ) (hi : i ≤ n) : HomologicalComplex (ModuleCat R) Periodic.PeriodicComplex.BundleCycles.periodicComplexShape :=
  EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (x ^ i) (x ^ (n - i)) (powerPeriodic_kill x n h i hi)

def powerPeriodicHomologyFinite (x : R) (n : ℕ) (h : ∀ m : M, x ^ n • m = 0) : Prop :=
  ∀ (i : ℕ) (hi : i ≤ n) (j : Bool),
    Module.length R ((powerPeriodicComplex x n h i hi).homology j) ≠ ⊤

def powerPeriodicEuler (x : R) (n : ℕ) (h : ∀ m : M, x ^ n • m = 0)
    (hf : powerPeriodicHomologyFinite x n h) (i : ℕ) (hi : i ≤ n) : ℤ :=
  Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (powerPeriodicComplex x n h i hi) (hf i hi false) (hf i hi true)

theorem powerPeriodicEuler_top (x : R) (n : ℕ) (h : ∀ m : M, x ^ n • m = 0)
    (hf : powerPeriodicHomologyFinite x n h) : powerPeriodicEuler x n h hf n le_rfl = 0 := by
  have hk : ∀ m : M, (x ^ n * 1) • m = 0 := by simpa only [mul_one] using h
  have hlen (j : Bool) : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (x ^ n) 1 hk).homology j) ≠ ⊤ := by
    have he := equationPeriodicHomology_length_congr (x ^ n) (x ^ (n - n)) (x ^ n) 1
      rfl (by simp) (powerPeriodic_kill x n h n le_rfl) hk j
    exact fun ht => hf n le_rfl j (he.trans ht)
  exact (equationPeriodicEulerLength_congr (x ^ n) (x ^ (n - n)) (x ^ n) 1 rfl (by simp)
    (powerPeriodic_kill x n h n le_rfl) hk (hf n le_rfl false) (hf n le_rfl true)
    (hlen false) (hlen true)).trans (equationPeriodicEulerLength_one_right _ hk _ _)

end

section

/-!
# LineBundleCycles: recurrence for complementary powers

The constructed factor cone gives e(i+1) = e(i) + e(1) for fixed
nilpotence exponent. The scalar identities are just the laws of powers.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem powerPeriodicEuler_succ (x : R) (n : ℕ) (h : ∀ m : M, x ^ n • m = 0)
    (hf : powerPeriodicHomologyFinite x n h) (i : ℕ) (hi : i + 1 ≤ n) :
    powerPeriodicEuler x n h hf (i + 1) hi =
      powerPeriodicEuler x n h hf i (by omega) + powerPeriodicEuler x n h hf 1 (by omega) := by
  have hi₀ : i ≤ n := by omega
  have hn : 1 ≤ n := by omega
  let a := x ^ i
  let b := x
  let c := x ^ (n - (i + 1))
  have hab : a * b = x ^ (i + 1) := (pow_succ x i).symm
  have hbc : b * c = x ^ (n - i) := by
    change x * x ^ (n - (i + 1)) = x ^ (n - i)
    rw [← pow_succ']
    congr 1
    omega
  have hac : a * c = x ^ (n - 1) := by
    change x ^ i * x ^ (n - (i + 1)) = x ^ (n - 1)
    rw [← pow_add]
    congr 1
    omega
  have hprod : ∀ m : M, (a * b * c) • m = 0 := by
    intro m
    rw [hab]
    exact powerPeriodic_kill x n h (i + 1) hi m
  let hA := Periodic.FactorKill.BundleCycles.factorCone_kill_source a b c hprod
  let hB := Periodic.FactorKill.BundleCycles.factorCone_kill_middle a b c hprod
  have hAB (j : Bool) : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (a * b) c hprod).homology j) ≠ ⊤ := by
    have he := equationPeriodicHomology_length_congr (a * b) c (x ^ (i + 1)) (x ^ (n - (i + 1)))
      hab rfl hprod (powerPeriodic_kill x n h (i + 1) hi) j
    exact fun ht => hf (i + 1) hi j (he.symm.trans ht)
  have hAF (j : Bool) : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex a (b * c) hA).homology j) ≠ ⊤ := by
    have he := equationPeriodicHomology_length_congr a (b * c) (x ^ i) (x ^ (n - i))
      rfl hbc hA (powerPeriodic_kill x n h i hi₀) j
    exact fun ht => hf i hi₀ j (he.symm.trans ht)
  have hBF (j : Bool) : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex b (a * c) hB).homology j) ≠ ⊤ := by
    have he := equationPeriodicHomology_length_congr b (a * c) (x ^ 1) (x ^ (n - 1))
      (by exact (pow_one x).symm) hac hB (powerPeriodic_kill x n h 1 hn) j
    exact fun ht => hf 1 hn j (he.symm.trans ht)
  have he := Periodic.FactorEuler.BundleCycles.periodicEulerLength_factor_comp a b c hprod
    (hAB false) (hAB true) (hAF false) (hAF true) (hBF false) (hBF true)
  have heAB := equationPeriodicEulerLength_congr (a * b) c (x ^ (i + 1)) (x ^ (n - (i + 1)))
    hab rfl hprod (powerPeriodic_kill x n h (i + 1) hi)
    (hAB false) (hAB true) (hf (i + 1) hi false) (hf (i + 1) hi true)
  have heA := equationPeriodicEulerLength_congr a (b * c) (x ^ i) (x ^ (n - i))
    rfl hbc hA (powerPeriodic_kill x n h i hi₀)
    (hAF false) (hAF true) (hf i hi₀ false) (hf i hi₀ true)
  have heB := equationPeriodicEulerLength_congr b (a * c) (x ^ 1) (x ^ (n - 1))
    (by exact (pow_one x).symm) hac hB (powerPeriodic_kill x n h 1 hn)
    (hBF false) (hBF true) (hf 1 hn false) (hf 1 hn true)
  exact heAB.symm.trans (he.trans (congrArg₂ (· + ·) heA heB))

end

/-!
# LineBundleCycles: vanishing for complementary nilpotent powers

Factor composition makes every Euler value i times the first value.
At the unit endpoint it is zero, so torsion-freeness of the integers
forces the first value, and hence every value, to vanish.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem powerPeriodicEuler_eq_mul (x : R) (n : ℕ) (h : ∀ m : M, x ^ n • m = 0)
    (hf : powerPeriodicHomologyFinite x n h) (hn : 1 ≤ n) (i : ℕ) (hi : i ≤ n) :
    powerPeriodicEuler x n h hf i hi = (i : ℤ) * powerPeriodicEuler x n h hf 1 hn := by
  have hzero : powerPeriodicEuler x n h hf 0 (Nat.zero_le n) = 0 := by
    have he := powerPeriodicEuler_succ x n h hf 0 hn
    change powerPeriodicEuler x n h hf 1 hn =
      powerPeriodicEuler x n h hf 0 (Nat.zero_le n) + powerPeriodicEuler x n h hf 1 hn at he
    omega
  induction i with
  | zero => simpa only [Nat.cast_zero, zero_mul] using hzero
  | succ i ih =>
    have hi₀ : i ≤ n := by omega
    rw [powerPeriodicEuler_succ x n h hf i hi, ih hi₀]
    push_cast
    ring

theorem powerPeriodicEuler_zero (x : R) (n : ℕ) (h : ∀ m : M, x ^ n • m = 0)
    (hf : powerPeriodicHomologyFinite x n h) (i : ℕ) (hi : i ≤ n) :
    powerPeriodicEuler x n h hf i hi = 0 := by
  by_cases hn : n = 0
  · subst n
    have hi₀ : i = 0 := by omega
    subst i
    exact powerPeriodicEuler_top x 0 h hf
  have hn₁ : 1 ≤ n := by omega
  have he := (powerPeriodicEuler_eq_mul x n h hf hn₁ n le_rfl).symm.trans
    (powerPeriodicEuler_top x n h hf)
  have hfirst : powerPeriodicEuler x n h hf 1 hn₁ = 0 :=
    (mul_eq_zero.mp he).resolve_left (by exact_mod_cast hn)
  rw [powerPeriodicEuler_eq_mul x n h hf hn₁ i hi, hfirst, mul_zero]

theorem nilpotentPeriodicEulerLength_zero (x : R) (n : ℕ) (h : ∀ m : M, x ^ n • m = 0)
    (hf : powerPeriodicHomologyFinite x n h) (i : ℕ) (hi : i ≤ n)
    (h₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (x ^ i) (x ^ (n - i))
      (powerPeriodic_kill x n h i hi)).homology false) ≠ ⊤)
    (h₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (x ^ i) (x ^ (n - i))
      (powerPeriodic_kill x n h i hi)).homology true) ≠ ⊤) :
    Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (x ^ i) (x ^ (n - i))
      (powerPeriodic_kill x n h i hi)) h₀ h₁ = 0 :=
  powerPeriodicEuler_zero x n h hf i hi

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.NilpotentPeriodic.BundleCycles
