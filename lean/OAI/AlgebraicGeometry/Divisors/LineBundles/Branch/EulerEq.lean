import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.ImageEuler
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PowerFiniteness
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.PowerExact
import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.FamilyEuler
import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.ScalingScale

/-! # Euler Eq -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EulerEq.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: branch Euler comparison with complementary powers -/

variable {R : Type*} [CommRing R] [IsDomain R]

variable [IsLocalRing R] [Ring.KrullDimLE 2 R] [IsNoetherianRing R]

theorem productBranchEuler_scaled_comparison (a b r q x y u v : R)
    (ha : a ≠ 0) (hb : b ≠ 0) (hdim : ringKrullDim R = 2)
    (P : Diagonal.BundleCycles.minimalBranchIndex (a * b))
    (hx : x ∉ P.1) (hy : y ∉ P.1) (hu : u ∉ P.1) (hv : v ∉ P.1)
    (heφ : x * a = u * r) (heψ : y * b = v * q)
    (hk : ∀ z : PeriodicComplex.BundleCycles.productBranchModule a b P.1, (r * q) • z = 0)
    (h₀ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (M := PeriodicComplex.BundleCycles.productBranchModule a b P.1) r q hk).homology false) ≠ ⊤)
    (h₁ : Module.length R ((EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (M := PeriodicComplex.BundleCycles.productBranchModule a b P.1) r q hk).homology true) ≠ ⊤) :
    FamilyEuler.BundleCycles.productBranchEuler a b ha hb P =
      Periodic.PeriodicComplex.BundleCycles.periodicEulerLength (EquationPeriodicComplex.BundleCycles.equationPeriodicComplex (M := PeriodicComplex.BundleCycles.productBranchModule a b P.1) r q hk) h₀ h₁ +
        ImageEuler.BundleCycles.branchImageEuler a b a x ha hb hdim P.1 P.2 hx -
        ImageEuler.BundleCycles.branchImageEuler a b b y ha hb hdim P.1 P.2 hy -
        ImageEuler.BundleCycles.branchImageEuler a b r u ha hb hdim P.1 P.2 hu +
        ImageEuler.BundleCycles.branchImageEuler a b q v ha hb hdim P.1 P.2 hv := by
  let M := PeriodicComplex.BundleCycles.productBranchModule a b P.1
  have hφ : x • MultiplicationSequence.BundleCycles.equationEndomorphism a M = u • MultiplicationSequence.BundleCycles.equationEndomorphism r M := by
    apply LinearMap.ext
    intro z
    change x • (a • z) = u • (r • z)
    rw [← mul_smul, heφ, mul_smul]
  have hψ : y • MultiplicationSequence.BundleCycles.equationEndomorphism b M = v • MultiplicationSequence.BundleCycles.equationEndomorphism q M := by
    apply LinearMap.ext
    intro z
    change y • (b • z) = v • (q • z)
    rw [← mul_smul, heψ, mul_smul]
  exact Periodic.ScalingScale.BundleCycles.periodicEulerLength_factorized x y u v
    (MultiplicationSequence.BundleCycles.equationEndomorphism a M) (MultiplicationSequence.BundleCycles.equationEndomorphism b M)
    (MultiplicationSequence.BundleCycles.equationEndomorphism r M) (MultiplicationSequence.BundleCycles.equationEndomorphism q M)
    (EquationPeriodicComplex.BundleCycles.equationPeriodic_comp_zero a b (Diagonal.BundleCycles.productBranch_annihilated a b P.1))
    (EquationPeriodicComplex.BundleCycles.equationPeriodic_comp_zero b a (EquationPeriodicComplex.BundleCycles.equationPeriodic_kill_swap a b (Diagonal.BundleCycles.productBranch_annihilated a b P.1)))
    (EquationPeriodicComplex.BundleCycles.equationPeriodic_comp_zero r q hk)
    (EquationPeriodicComplex.BundleCycles.equationPeriodic_comp_zero q r (EquationPeriodicComplex.BundleCycles.equationPeriodic_kill_swap r q hk)) hφ hψ
    (PeriodicComplex.BundleCycles.productBranch_denominator_injective a b P.1 x hx) (PeriodicComplex.BundleCycles.productBranch_denominator_injective a b P.1 y hy)
    (PeriodicComplex.BundleCycles.productBranch_denominator_injective a b P.1 u hu) (PeriodicComplex.BundleCycles.productBranch_denominator_injective a b P.1 v hv)
    (Diagonal.BundleCycles.productBranchPeriodicComplex_homology_length_ne_top a b ha hb P.1 P.2 false)
    (Diagonal.BundleCycles.productBranchPeriodicComplex_homology_length_ne_top a b ha hb P.1 P.2 true) h₀ h₁
    (ImageEuler.BundleCycles.branchImage_equation_lengths_finite a b a x ha hb hdim P.1 P.2 hx).1
    (ImageEuler.BundleCycles.branchImage_equation_lengths_finite a b a x ha hb hdim P.1 P.2 hx).2
    (ImageEuler.BundleCycles.branchImage_equation_lengths_finite a b b y ha hb hdim P.1 P.2 hy).1
    (ImageEuler.BundleCycles.branchImage_equation_lengths_finite a b b y ha hb hdim P.1 P.2 hy).2
    (ImageEuler.BundleCycles.branchImage_equation_lengths_finite a b r u ha hb hdim P.1 P.2 hu).1
    (ImageEuler.BundleCycles.branchImage_equation_lengths_finite a b r u ha hb hdim P.1 P.2 hu).2
    (ImageEuler.BundleCycles.branchImage_equation_lengths_finite a b q v ha hb hdim P.1 P.2 hv).1
    (ImageEuler.BundleCycles.branchImage_equation_lengths_finite a b q v ha hb hdim P.1 P.2 hv).2

end

section

/-! # LineBundleCycles: branch Euler comparison with complementary powers -/

variable {R : Type*} [CommRing R] [IsDomain R]

variable [IsLocalRing R] [Ring.KrullDimLE 2 R] [IsNoetherianRing R]

theorem productBranchEuler_factorized (a b t u s v w : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (m n : ℕ) (P : Diagonal.BundleCycles.minimalBranchIndex (a * b))
    [IsDiscreteValuationRing (Localization P.1.primeCompl)]
    (ht : Irreducible (algebraMap R (Localization P.1.primeCompl) t))
    (hu : u ∉ P.1) (hs : s ∉ P.1) (hv : v ∉ P.1) (hw : w ∉ P.1)
    (hsa : s * a = u * t ^ m) (hwb : w * b = v * t ^ n) :
    FamilyEuler.BundleCycles.productBranchEuler a b ha hb P =
      ImageEuler.BundleCycles.branchImageEuler a b a s ha hb hdim P.1 P.2 hs -
        ImageEuler.BundleCycles.branchImageEuler a b b w ha hb hdim P.1 P.2 hw -
        ImageEuler.BundleCycles.branchImageEuler a b (t ^ m) u ha hb hdim P.1 P.2 hu +
        ImageEuler.BundleCycles.branchImageEuler a b (t ^ n) v ha hb hdim P.1 P.2 hv := by
  have hI := PowerExact.BundleCycles.branchUniformizer_localized_product_ideal a b t u s v w m n P.1 hu hs hv hw hsa hwb
  have hk := PowerExact.BundleCycles.branchUniformizerPower_annihilates a b t u s v w m n P.1 hu hv hsa hwb
  have hp := PowerFiniteness.BundleCycles.branchPowerPair_kill a b t m n P.1 hk
  have hp₀ := PowerFiniteness.BundleCycles.branchPowerPair_homology_finite a b t ha hb m n P.1 P.2 ht.ne_zero hI hk false
  have hp₁ := PowerFiniteness.BundleCycles.branchPowerPair_homology_finite a b t ha hb m n P.1 P.2 ht.ne_zero hI hk true
  have he := productBranchEuler_scaled_comparison a b (t ^ m) (t ^ n) s w u v ha hb hdim P
    hs hw hu hv hsa hwb hp hp₀ hp₁
  rw [PowerFiniteness.BundleCycles.branchPowerPair_Euler_zero a b t ha hb m n P.1 P.2 ht.ne_zero hI hk hp₀ hp₁, zero_add] at he
  exact he

end

/-!
# LineBundleCycles: the actual branch Euler coefficient

Cleared DVR factorizations identify two scaled pairs of actual
differentials. Scaling, nilpotent-power vanishing, and the computed
image lengths give the branch coefficient in prime quotient lengths.
-/

variable {R : Type*} [CommRing R] [IsDomain R]

theorem branchFactor_order (P : Ideal R) [P.IsPrime]
    [IsDiscreteValuationRing (Localization P.primeCompl)]
    (a t u s : R) (m : ℕ) (ht : Irreducible (algebraMap R (Localization P.primeCompl) t))
    (hu : u ∉ P) (hs : s ∉ P) (ha : s * a = u * t ^ m) :
    Ring.ord (Localization P.primeCompl) (algebraMap R (Localization P.primeCompl) a) = m := by
  let A := Localization P.primeCompl
  have he : algebraMap R A s * algebraMap R A a = algebraMap R A u * (algebraMap R A t) ^ m := by
    rw [← map_mul, ha, map_mul, map_pow]
  have ho := congrArg (Ring.ord A) he
  rw [Ring.ord_mul_of_isUnit_left (IsLocalization.map_units A (⟨s, hs⟩ : P.primeCompl)),
    Ring.ord_mul_of_isUnit_left (IsLocalization.map_units A (⟨u, hu⟩ : P.primeCompl)),
    Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero), Ring.ord_of_irreducible ht] at ho
  simpa only [nsmul_eq_mul, mul_one] using ho

variable [IsLocalRing R] [Ring.KrullDimLE 2 R] [IsNoetherianRing R]

theorem productBranchEuler_eq_factor_orders (a b t u s v w : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdim : ringKrullDim R = 2) (m n : ℕ) (P : Diagonal.BundleCycles.minimalBranchIndex (a * b))
    [IsDiscreteValuationRing (Localization P.1.primeCompl)]
    (ht : Irreducible (algebraMap R (Localization P.1.primeCompl) t))
    (hu : u ∉ P.1) (hs : s ∉ P.1) (hv : v ∉ P.1) (hw : w ∉ P.1)
    (hsa : s * a = u * t ^ m) (hwb : w * b = v * t ^ n) :
    FamilyEuler.BundleCycles.productBranchEuler a b ha hb P =
      (n : ℤ) * (PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength s P.1 - PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength u P.1) +
      (m : ℤ) * (PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength v P.1 - PrimeIntersectionLength.BundleCycles.primeIntersectionQuotientLength w P.1) := by
  have hI := PowerExact.BundleCycles.branchUniformizer_localized_product_ideal a b t u s v w m n P.1 hu hs hv hw hsa hwb
  have hI' : (Ideal.span {a * b}).map (algebraMap R (Localization P.1.primeCompl)) =
      Ideal.span {(algebraMap R (Localization P.1.primeCompl) t) ^ (n + m)} := by
    simpa only [Nat.add_comm n m] using hI
  rw [productBranchEuler_factorized a b t u s v w ha hb hdim m n P ht hu hs hv hw hsa hwb,
    ImageEuler.BundleCycles.branchImageEuler_eq_local_length a b a s ha hb hdim P.1 P.2 hs,
    ImageEuler.BundleCycles.branchImageEuler_eq_local_length a b b w ha hb hdim P.1 P.2 hw,
    ImageEuler.BundleCycles.branchImageEuler_eq_local_length a b (t ^ m) u ha hb hdim P.1 P.2 hu,
    ImageEuler.BundleCycles.branchImageEuler_eq_local_length a b (t ^ n) v ha hb hdim P.1 P.2 hv,
    ImageLength.BundleCycles.productBranchImage_local_length_left a b ha P.1,
    ImageLength.BundleCycles.productBranchImage_local_length_right a b hb P.1,
    branchFactor_order P.1 b t v w n ht hv hw hwb,
    branchFactor_order P.1 a t u s m ht hu hs hsa,
    ImageLength.BundleCycles.branchPowersImage_local_length a b t m n P.1 ht hI,
    ImageLength.BundleCycles.branchPowersImage_local_length a b t n m P.1 ht hI']
  simp only [ENat.toNat_natCast]
  ring

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.EulerEq.BundleCycles
