import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.LocalFiniteness
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PowerExact
import OAI.AlgebraicGeometry.Divisors.LineBundles.NilpotentPeriodic

/-! # Power Finiteness -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PowerFiniteness.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: finite homology and zero Euler value for actual branch powers

The computed local quotient makes every complementary power pair
exact at P. The branch support theorem supplies finiteness everywhere,
so the proved nilpotent-power vanishing applies to the actual module.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Ring.KrullDimLE 2 R] [IsNoetherianRing R]

theorem branchPower_homology_finite (a b t : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (N : ℕ) (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {a * b}).minimalPrimes)
    (ht : algebraMap R (Localization P.primeCompl) t ≠ 0)
    (hI : (Ideal.span {a * b}).map (algebraMap R (Localization P.primeCompl)) =
      Ideal.span {(algebraMap R (Localization P.primeCompl) t) ^ N})
    (hkill : ∀ z : PeriodicComplex.BundleCycles.productBranchModule a b P, t ^ N • z = 0) :
    NilpotentPeriodic.BundleCycles.powerPeriodicHomologyFinite (M := PeriodicComplex.BundleCycles.productBranchModule a b P) t N hkill := by
  intro i hi j
  cases j
  · unfold NilpotentPeriodic.BundleCycles.powerPeriodicComplex EquationPeriodicComplex.BundleCycles.equationPeriodicComplex
    rw [(Periodic.Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso _ _ _ _).toLinearEquiv.length_eq]
    apply LocalFiniteness.BundleCycles.branchPeriodicHomology_length_ne_top a b ha hb P hP _ _ _
    simp only [LocalizedEquationExact.BundleCycles.localizedEndomorphism_equation]
    exact PowerExact.BundleCycles.branchPower_local_exact a b t N (N - i) i (Nat.sub_add_cancel hi) P ht hI
  · unfold NilpotentPeriodic.BundleCycles.powerPeriodicComplex EquationPeriodicComplex.BundleCycles.equationPeriodicComplex
    rw [(Periodic.Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso _ _ _ _).toLinearEquiv.length_eq]
    apply LocalFiniteness.BundleCycles.branchPeriodicHomology_length_ne_top a b ha hb P hP _ _ _
    simp only [LocalizedEquationExact.BundleCycles.localizedEndomorphism_equation]
    exact PowerExact.BundleCycles.branchPower_local_exact a b t N i (N - i) (Nat.add_sub_of_le hi) P ht hI

theorem branchPower_Euler_zero (a b t : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (N : ℕ) (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {a * b}).minimalPrimes)
    (ht : algebraMap R (Localization P.primeCompl) t ≠ 0)
    (hI : (Ideal.span {a * b}).map (algebraMap R (Localization P.primeCompl)) =
      Ideal.span {(algebraMap R (Localization P.primeCompl) t) ^ N})
    (hkill : ∀ z : PeriodicComplex.BundleCycles.productBranchModule a b P, t ^ N • z = 0) (i : ℕ) (hi : i ≤ N) :
    NilpotentPeriodic.BundleCycles.powerPeriodicEuler (M := PeriodicComplex.BundleCycles.productBranchModule a b P) t N hkill (branchPower_homology_finite a b t ha hb N P hP ht hI hkill) i hi = 0 :=
  NilpotentPeriodic.BundleCycles.powerPeriodicEuler_zero (M := PeriodicComplex.BundleCycles.productBranchModule a b P) t N hkill _ i hi

end

/-!
# LineBundleCycles: complementary branch powers in two-exponent notation
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Ring.KrullDimLE 2 R] [IsNoetherianRing R]

omit [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 2 R] [IsNoetherianRing R] in
theorem branchPowerPair_kill (a b t : R) (m n : ℕ) (P : Ideal R) [P.IsPrime]
    (hkill : ∀ z : PeriodicComplex.BundleCycles.productBranchModule a b P, t ^ (m + n) • z = 0) :
    ∀ z : PeriodicComplex.BundleCycles.productBranchModule a b P, (t ^ m * t ^ n) • z = 0 := by
  simpa only [← pow_add] using hkill

theorem branchPowerPair_homology_finite (a b t : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (m n : ℕ) (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {a * b}).minimalPrimes)
    (ht : algebraMap R (Localization P.primeCompl) t ≠ 0)
    (hI : (Ideal.span {a * b}).map (algebraMap R (Localization P.primeCompl)) =
      Ideal.span {(algebraMap R (Localization P.primeCompl) t) ^ (m + n)})
    (hkill : ∀ z : PeriodicComplex.BundleCycles.productBranchModule a b P, t ^ (m + n) • z = 0) (i : Bool) :
    Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (M := PeriodicComplex.BundleCycles.productBranchModule a b P) (t ^ m) (t ^ n)
      (branchPowerPair_kill a b t m n P hkill)).homology i) ≠ ⊤ := by
  have hf := branchPower_homology_finite a b t ha hb (m + n) P hP ht hI hkill m (Nat.le_add_right m n) i
  have he := NilpotentPeriodic.BundleCycles.equationPeriodicHomology_length_congr (M := PeriodicComplex.BundleCycles.productBranchModule a b P)
    (t ^ m) (t ^ (m + n - m)) (t ^ m) (t ^ n) rfl
    (congrArg (fun k : ℕ => t ^ k) (Nat.add_sub_cancel_left m n))
    (NilpotentPeriodic.BundleCycles.powerPeriodic_kill t (m + n) hkill m (Nat.le_add_right m n))
    (branchPowerPair_kill a b t m n P hkill) i
  exact he ▸ hf

theorem branchPowerPair_Euler_zero (a b t : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (m n : ℕ) (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {a * b}).minimalPrimes)
    (ht : algebraMap R (Localization P.primeCompl) t ≠ 0)
    (hI : (Ideal.span {a * b}).map (algebraMap R (Localization P.primeCompl)) =
      Ideal.span {(algebraMap R (Localization P.primeCompl) t) ^ (m + n)})
    (hkill : ∀ z : PeriodicComplex.BundleCycles.productBranchModule a b P, t ^ (m + n) • z = 0)
    (h₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (M := PeriodicComplex.BundleCycles.productBranchModule a b P) (t ^ m) (t ^ n)
      (branchPowerPair_kill a b t m n P hkill)).homology false) ≠ ⊤)
    (h₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (M := PeriodicComplex.BundleCycles.productBranchModule a b P) (t ^ m) (t ^ n)
      (branchPowerPair_kill a b t m n P hkill)).homology true) ≠ ⊤) :
    Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (M := PeriodicComplex.BundleCycles.productBranchModule a b P) (t ^ m) (t ^ n)
      (branchPowerPair_kill a b t m n P hkill)) h₀ h₁ = 0 := by
  let hf := branchPower_homology_finite a b t ha hb (m + n) P hP ht hI hkill
  have he := NilpotentPeriodic.BundleCycles.equationPeriodicEulerLength_congr (M := PeriodicComplex.BundleCycles.productBranchModule a b P)
    (t ^ m) (t ^ (m + n - m)) (t ^ m) (t ^ n) rfl
    (congrArg (fun k : ℕ => t ^ k) (Nat.add_sub_cancel_left m n))
    (NilpotentPeriodic.BundleCycles.powerPeriodic_kill t (m + n) hkill m (Nat.le_add_right m n))
    (branchPowerPair_kill a b t m n P hkill)
    (hf m (Nat.le_add_right m n) false) (hf m (Nat.le_add_right m n) true) h₀ h₁
  exact he.symm.trans (branchPower_Euler_zero a b t ha hb (m + n) P hP ht hI hkill m (Nat.le_add_right m n))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PowerFiniteness.BundleCycles
