import OAI.AlgebraicGeometry.Divisors.LineBundles.MinimalBranchSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationExact
import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfacePrimeFactors

/-! # Diagonal -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.Diagonal.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: finite homology for every actual branch complex on a local surface

At its defining prime the branch complex is exact. Away from that
prime and the closed point, its underlying module vanishes. Thus its
actual periodic homology is supported only at the closed point.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 2 R]

theorem surfaceMinimalPrime_le_eq_of_not_maximal (r : R) (hr : r ≠ 0)
    (P : Ideal R) (hP : P ∈ (Ideal.span {r}).minimalPrimes) (q : PrimeSpectrum R)
    (hqm : q.asIdeal ≠ IsLocalRing.maximalIdeal R) (hpq : P ≤ q.asIdeal) : q.asIdeal = P := by
  let branchSupportPrime : q.asIdeal.IsPrime := q.isPrime
  have hrq : r ∈ q.asIdeal := hpq (hP.le (Ideal.subset_span (Set.mem_singleton r)))
  have hq := (SurfacePrimeFactors.BundleCycles.surfacePrime_minimal_or_maximal r hr q.asIdeal hrq).resolve_right hqm
  exact le_antisymm (hq.2 ⟨hP.isPrime, hP.le⟩ hpq) hpq

theorem productBranch_localized_exact_off_closed
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {a * b}).minimalPrimes) (q : PrimeSpectrum R)
    (hqm : q.asIdeal ≠ IsLocalRing.maximalIdeal R) :
    Function.Exact
        (Periodic.Localization.BundleCycles.localizedEndomorphism q.asIdeal.primeCompl (MultiplicationSequence.BundleCycles.equationEndomorphism a (PeriodicComplex.BundleCycles.productBranchModule a b P)))
        (Periodic.Localization.BundleCycles.localizedEndomorphism q.asIdeal.primeCompl (MultiplicationSequence.BundleCycles.equationEndomorphism b (PeriodicComplex.BundleCycles.productBranchModule a b P))) ∧
      Function.Exact
        (Periodic.Localization.BundleCycles.localizedEndomorphism q.asIdeal.primeCompl (MultiplicationSequence.BundleCycles.equationEndomorphism b (PeriodicComplex.BundleCycles.productBranchModule a b P)))
        (Periodic.Localization.BundleCycles.localizedEndomorphism q.asIdeal.primeCompl (MultiplicationSequence.BundleCycles.equationEndomorphism a (PeriodicComplex.BundleCycles.productBranchModule a b P))) := by
  by_cases hpq : P ≤ q.asIdeal
  · have he := surfaceMinimalPrime_le_eq_of_not_maximal (a * b) (mul_ne_zero ha hb) P hP q hqm hpq
    subst P
    simp only [LocalizedEquationExact.BundleCycles.localizedEndomorphism_equation]
    exact ⟨LocalizedEquationExact.BundleCycles.productBranch_local_exact a b hb q.asIdeal, LocalizedEquationExact.BundleCycles.productBranch_local_exact_reverse a b ha q.asIdeal⟩
  · have hz : Subsingleton (LocalizedModule q.asIdeal.primeCompl (PeriodicComplex.BundleCycles.productBranchModule a b P)) :=
      MinimalBranchSupport.BundleCycles.minimalPrime_branch_localization_zero (Ideal.span {a * b}) P hP q hpq
    constructor <;> intro m <;> constructor
    · intro _
      exact ⟨0, hz.elim _ _⟩
    · intro _
      exact hz.elim _ _
    · intro _
      exact ⟨0, hz.elim _ _⟩
    · intro _
      exact hz.elim _ _

variable [IsNoetherianRing R]

theorem productBranchPeriodicComplex_homology_length_ne_top
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (P : Ideal R) [P.IsPrime]
    (hP : P ∈ (Ideal.span {a * b}).minimalPrimes) (i : Bool) :
    Module.length R ((PeriodicComplex.BundleCycles.productBranchPeriodicComplex a b P).homology i) ≠ ⊤ := by
  cases i
  · unfold PeriodicComplex.BundleCycles.productBranchPeriodicComplex
    rw [(Periodic.Exact.BundleCycles.endomorphismPeriodicComplex_homology_false_iso _ _ _ _).toLinearEquiv.length_eq]
    exact Periodic.Localization.BundleCycles.periodicHomology_length_ne_top_of_local_exact _ _ _
      (fun q hqm => (productBranch_localized_exact_off_closed a b ha hb P hP q hqm).2)
  · unfold PeriodicComplex.BundleCycles.productBranchPeriodicComplex
    rw [(Periodic.Exact.BundleCycles.endomorphismPeriodicComplex_homology_true_iso _ _ _ _).toLinearEquiv.length_eq]
    exact Periodic.Localization.BundleCycles.periodicHomology_length_ne_top_of_local_exact _ _ _
      (fun q hqm => (productBranch_localized_exact_off_closed a b ha hb P hP q hqm).1)

end

section

/-!
# LineBundleCycles: the actual diagonal map to all minimal branch images
-/

variable {R : Type*} [CommRing R]

abbrev minimalBranchIndex (r : R) := {P : Ideal R // P ∈ (Ideal.span {r}).minimalPrimes}

instance minimalBranchIndex_prime (r : R) (P : minimalBranchIndex r) : P.1.IsPrime := P.2.isPrime

instance minimalBranchIndex_fintype [IsNoetherianRing R] (r : R) : Fintype (minimalBranchIndex r) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {r})).fintype

abbrev productBranchFamily (a b : R) := ∀ P : minimalBranchIndex (a * b), PeriodicComplex.BundleCycles.productBranchModule a b P.1

def productBranchDiagonal (a b : R) : ProductPeriodicComplex.BundleCycles.productEquationQuotient a b →ₗ[R] productBranchFamily a b :=
  LinearMap.pi (fun P => LocalizationImage.BundleCycles.localizationImageProjection P.1.primeCompl)

theorem productEquation_annihilated (a b : R) (m : ProductPeriodicComplex.BundleCycles.productEquationQuotient a b) :
    (a * b) • m = 0 :=
  (mul_smul a b m).trans (LinearMap.congr_fun (ProductPeriodicComplex.BundleCycles.productEquation_comp_zero_reverse a b) m)

theorem productBranch_annihilated (a b : R) (P : Ideal R) [P.IsPrime]
    (m : PeriodicComplex.BundleCycles.productBranchModule a b P) : (a * b) • m = 0 := by
  obtain ⟨u, rfl⟩ := LocalizationImage.BundleCycles.localizationImageProjection_surjective P.primeCompl m
  let f := LocalizationImage.BundleCycles.localizationImageProjection (M := ProductPeriodicComplex.BundleCycles.productEquationQuotient a b) P.primeCompl
  exact (f.map_smul (a * b) u).symm.trans
    ((congrArg f (productEquation_annihilated a b u)).trans f.map_zero)

theorem productBranchFamily_annihilated (a b : R) (m : productBranchFamily a b) :
    (a * b) • m = 0 := by
  funext P
  exact productBranch_annihilated a b P.1 (m P)

end

section

/-!
# LineBundleCycles: the diagonal kernel is supported at the closed point

A nonclosed prime containing ab is one of the indexed minimal primes.
The corresponding component of the actual diagonal then detects its
localized kernel. Outside V(ab), the annihilating product is invertible.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 2 R]

theorem productBranchDiagonal_kernel_localization_zero
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (q : PrimeSpectrum R)
    (hqm : q.asIdeal ≠ IsLocalRing.maximalIdeal R) :
    Subsingleton (LocalizedModule q.asIdeal.primeCompl (productBranchDiagonal a b).ker) := by
  apply LocalizedModule.subsingleton_iff.mpr
  intro x
  by_cases hrq : a * b ∈ q.asIdeal
  · let diagonalKernelPrime : q.asIdeal.IsPrime := q.isPrime
    have hq := (SurfacePrimeFactors.BundleCycles.surfacePrime_minimal_or_maximal (a * b) (mul_ne_zero ha hb) q.asIdeal hrq).resolve_right hqm
    let Q : minimalBranchIndex (a * b) := ⟨q.asIdeal, hq⟩
    have hx : LocalizedModule.mkLinearMap q.asIdeal.primeCompl (ProductPeriodicComplex.BundleCycles.productEquationQuotient a b) x.1 = 0 :=
      congrArg (fun v : productBranchFamily a b =>
        ((v Q) : LocalizedModule q.asIdeal.primeCompl (ProductPeriodicComplex.BundleCycles.productEquationQuotient a b))) x.2
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := q.asIdeal.primeCompl)
      (f := LocalizedModule.mkLinearMap q.asIdeal.primeCompl (ProductPeriodicComplex.BundleCycles.productEquationQuotient a b))
      (hx.trans (map_zero _).symm)
    refine ⟨s.1, s.2, Subtype.ext ?_⟩
    exact hs.trans (smul_zero s)
  · exact ⟨a * b, hrq, Subtype.ext (productEquation_annihilated a b x.1)⟩

theorem productBranchDiagonal_kernel_length_ne_top [IsNoetherianRing R]
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.length R (productBranchDiagonal a b).ker ≠ ⊤ :=
  Closed.SupportLength.BundleCycles.moduleLength_ne_top_of_localizations_zero
    (productBranchDiagonal_kernel_localization_zero a b ha hb)

end

/-!
# LineBundleCycles: the diagonal cokernel is supported at the closed point

At a minimal prime, lift the tuple's component on that branch. Every
remaining component vanishes after localization. A finite product of
their denominators clears the whole tuple in the actual cokernel.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Ring.KrullDimLE 2 R] [IsNoetherianRing R]

theorem productBranchDiagonal_cokernel_localization_zero
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (q : PrimeSpectrum R)
    (hqm : q.asIdeal ≠ IsLocalRing.maximalIdeal R) :
    Subsingleton (LocalizedModule q.asIdeal.primeCompl
      (productBranchFamily a b ⧸ (productBranchDiagonal a b).range)) := by
  classical
  apply LocalizedModule.subsingleton_iff.mpr
  intro z
  obtain ⟨u, rfl⟩ := (productBranchDiagonal a b).range.mkQ_surjective z
  by_cases hrq : a * b ∈ q.asIdeal
  · let diagonalCokernelPrime : q.asIdeal.IsPrime := q.isPrime
    have hq := (SurfacePrimeFactors.BundleCycles.surfacePrime_minimal_or_maximal (a * b) (mul_ne_zero ha hb) q.asIdeal hrq).resolve_right hqm
    let Q : minimalBranchIndex (a * b) := ⟨q.asIdeal, hq⟩
    obtain ⟨m, hm⟩ := LocalizationImage.BundleCycles.localizationImageProjection_surjective q.asIdeal.primeCompl (u Q)
    let v : productBranchFamily a b := u - productBranchDiagonal a b m
    have hvQ : v Q = 0 := by
      change u Q - LocalizationImage.BundleCycles.localizationImageProjection q.asIdeal.primeCompl m = 0
      rw [hm, sub_self]
    have hden : ∀ P : minimalBranchIndex (a * b), ∃ s : R, s ∉ q.asIdeal ∧ s • v P = 0 := by
      intro P
      by_cases hPQ : P = Q
      · subst P
        exact ⟨1, q.asIdeal.primeCompl.one_mem,
          (one_smul R (v Q)).trans hvQ⟩
      · have hnot : ¬ P.1 ≤ q.asIdeal := by
          intro hpq
          apply hPQ
          apply Subtype.ext
          exact le_antisymm hpq (hq.2 ⟨P.2.isPrime, P.2.le⟩ hpq)
        have hz := MinimalBranchSupport.BundleCycles.minimalPrime_branch_localization_zero (Ideal.span {a * b}) P.1 P.2 q hnot
        exact LocalizedModule.subsingleton_iff.mp hz (v P)
    choose s hs hs0 using hden
    let r : R := ∏ P : minimalBranchIndex (a * b), s P
    have hr : r ∉ q.asIdeal := q.asIdeal.primeCompl.prod_mem (fun P _ => hs P)
    have hv : r • v = 0 := by
      funext P
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ P)
      change r • v P = 0
      calc
        r • v P = k • (s P • v P) :=
          (congrArg (fun z : R => z • v P) hk).trans
            ((mul_smul (s P) k (v P)).trans (smul_comm (s P) k (v P)))
        _ = 0 := by rw [hs0 P, smul_zero]
    have hu : r • u = productBranchDiagonal a b (r • m) := by
      rw [(productBranchDiagonal a b).map_smul]
      apply sub_eq_zero.mp
      exact (smul_sub r u (productBranchDiagonal a b m)).symm.trans hv
    refine ⟨r, hr, ?_⟩
    change (productBranchDiagonal a b).range.mkQ (r • u) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨r • m, hu.symm⟩
  · refine ⟨a * b, hrq, ?_⟩
    change (productBranchDiagonal a b).range.mkQ ((a * b) • u) = 0
    rw [productBranchFamily_annihilated, map_zero]

theorem productBranchDiagonal_cokernel_length_ne_top
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.length R (productBranchFamily a b ⧸ (productBranchDiagonal a b).range) ≠ ⊤ :=
  Closed.SupportLength.BundleCycles.moduleLength_ne_top_of_localizations_zero
    (productBranchDiagonal_cokernel_localization_zero a b ha hb)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.Diagonal.BundleCycles
