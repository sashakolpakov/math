import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FixedPrimeFiltration
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ExternalDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.MultiplicitySum

/-! # Local Weighted Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalWeightedEuler

noncomputable section

/-! The native finite modules of a smooth stalk admit a top-dimensional
Euler expansion. The weights are the lengths at the actual stalk primes;
no affine presentation of the modules is required. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SpectrumRank

theorem quotient_bound (K A R : Type) [Field K] [CommRing A] [CommRing R]
    [Algebra K A] [Algebra.FiniteType K A] [Algebra A R]
    (q p : PrimeSpectrum R) (hp : p ∈ Module.support R (R ⧸ q.asIdeal)) :
    Affine.SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) p) ≤
      Affine.SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) q) := by
  have hle : q.asIdeal ≤ p.asIdeal := by
    simpa only [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker,
      PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] using hp
  exact (Affine.SpectrumRank.strict K A).antitone (Ideal.comap_mono hle)

theorem exists_data (K A R : Type) [Field K] [CommRing A] [CommRing R]
    [Algebra K A] [Algebra K R] [Algebra A R] [IsScalarTower K A R] [IsLocalRing R]
    (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d K A]
    (x : PrimeSpectrum A) [IsLocalization x.asIdeal.primeCompl R]
    (M : ModuleCat R) [Module.Finite R M] (r : ℕ)
    (hM : ∀ q ∈ Module.support R M,
      Affine.SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) q) ≤ r) :
    ∃ F : Finset (PrimeSpectrum R),
      (∀ q ∈ F, q ∈ Module.support R M ∧
        Affine.SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) q) = r ∧
        FiltrationBaseLength.length R (Localization.AtPrime q.asIdeal) M ≠ ⊤) ∧
      (∀ q, Affine.SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) q) = r → q ∉ F →
        FiltrationBaseLength.length R (Localization.AtPrime q.asIdeal) M = 0) ∧
      ∀ (N : ModuleCat R) [Module.Finite R N] [HasProjectiveDimensionLE N d] (s : ℕ)
        (_hN : ∀ q ∈ Module.support R N,
          Affine.SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) q) ≤ s)
        (_heq : r + s = d + Affine.SpectrumRank.dimension K A x)
        (_hi : Module.support R M ∩ Module.support R N ⊆ {IsLocalRing.closedPoint R}),
        Tor.Euler.euler R M N d =
          ∑ q ∈ F, ((FiltrationBaseLength.length R (Localization.AtPrime q.asIdeal) M).toNat : ℚ) *
            Tor.Euler.euler R (.of R (R ⧸ q.asIdeal)) N d := by
  let : Algebra.IsStandardSmooth K A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let : IsNoetherianRing R := IsLocalization.isNoetherianRing x.asIdeal.primeCompl R inferInstance
  let ρ : PrimeSpectrum R → ℕ := fun q => Affine.SpectrumRank.dimension K A (PrimeSpectrum.comap (algebraMap A R) q)
  have hρ : StrictAnti ρ := (Affine.SpectrumRank.strict K A).comp_strictMono
    (Tensor.LocalizationSpectrum.strict_comap A R x.asIdeal.primeCompl)
  obtain ⟨k, q, hsupp, hcount, he⟩ := FixedPrimeFiltration.exists_data R M
  have hdim (i : Fin k) : ρ (q i) ≤ r :=
    hM (q i) (hsupp i (MinimalPrimeFiltration.prime_mem_support R (q i)))
  let P := fun v : PrimeSpectrum R => ρ v = r
  let F := (Finset.univ.image q).filter P
  have hc (v : PrimeSpectrum R) (hv : P v) :
      FiltrationBaseLength.length R (Localization.AtPrime v.asIdeal) M =
        (Finset.univ.filter (fun i => q i = v)).card := by
    apply hcount
    intro w hw hwv
    by_contra hne
    have hlt := hρ (lt_of_le_of_ne hwv hne)
    have hwr := hM w hw
    change ρ w ≤ r at hwr
    change ρ v = r at hv
    omega
  refine ⟨F, ?_, ?_, ?_⟩
  · intro v hv
    have hP := (Finset.mem_filter.mp hv).2
    have hs : v ∈ Module.support R M := by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hv).1
      exact hsupp i (MinimalPrimeFiltration.prime_mem_support R (q i))
    refine ⟨hs, hP, ?_⟩
    rw [hc v hP]
    exact ENat.natCast_ne_top _
  · intro v hv hvF
    rw [hc v hv]
    have hempty : Finset.univ.filter (fun i => q i = v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hvF (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, hv⟩)
    rw [hempty, Finset.card_empty, Nat.cast_zero]
  · intro N _ _ s hN heq hi
    rw [he N d (IsLocalRing.closedPoint R) hi]
    have hfilter : (∑ i ∈ Finset.univ.filter (fun i => P (q i)),
        Tor.Euler.euler R (.of R (R ⧸ (q i).asIdeal)) N d) =
        ∑ i : Fin k, Tor.Euler.euler R (.of R (R ⧸ (q i).asIdeal)) N d := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi' hnot
      have hne : ρ (q i) ≠ r := fun h => hnot (Finset.mem_filter.mpr ⟨hi', h⟩)
      have hsmall : ρ (q i) + s < d + Affine.SpectrumRank.dimension K A x := by
        have hle := hdim i
        omega
      apply Affine.ExternalDimension.StandardSmoothEuler.euler_zero K A R d x (.of R (R ⧸ (q i).asIdeal)) N
        (ρ (q i)) s (quotient_bound K A R (q i)) hN hsmall
      exact (Set.inter_subset_inter_left _ (hsupp i)).trans hi
    rw [← hfilter]
    simpa only [P, F, Finset.filter_congr_decidable] using ProjectionFormula.Finite.MultiplicitySum.reindex k q P
      (fun v => FiltrationBaseLength.length R (Localization.AtPrime v.asIdeal) M) hc
      (fun v => Tor.Euler.euler R (.of R (R ⧸ v.asIdeal)) N d)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.LocalWeightedEuler
