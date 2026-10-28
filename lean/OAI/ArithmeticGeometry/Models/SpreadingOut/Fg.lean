import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-! # Fg -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.Fg.Construction

noncomputable section

/-!
Arithmetic ingredients for SpreadingOut. These declarations use only proved mathlib
results and do not import the statement specification or any project stubs.
-/

universe u

open TensorProduct
open scoped nonZeroDivisors

/-- A finitely generated subalgebra of a fraction field is contained in the
subalgebra obtained by inverting one nonzero denominator. -/
theorem fg_subalgebra_le_adjoin_inverse
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (A : Subalgebra R K) (hA : A.FG) :
    ∃ d : R, d ≠ 0 ∧
      A ≤ Algebra.adjoin R ({(algebraMap R K d)⁻¹} : Set K) := by
  classical
  obtain ⟨s, hs⟩ := hA
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) s
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hdk : algebraMap R K (d : R) ≠ 0 :=
    by
      intro h
      apply hd0
      apply IsFractionRing.injective R K
      exact h.trans (map_zero _).symm
  refine ⟨d, hd0, ?_⟩
  rw [← hs, Algebra.adjoin_le_iff]
  intro x hx
  obtain ⟨a, ha⟩ := hd x hx
  have heq : x = algebraMap R K a * (algebraMap R K (d : R))⁻¹ := by
    rw [ha, Algebra.smul_def, mul_comm (algebraMap R K (d : R)) x,
      mul_assoc, mul_inv_cancel₀ hdk, mul_one]
  rw [heq]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a)
    (Algebra.subset_adjoin (Set.mem_singleton _))

/-- Removing the primes containing a nonzero element removes finitely
many points from the prime spectrum of a ring with finite quotients. -/
theorem finite_complement_basicOpen
    {R : Type*} [CommRing R] [Ring.HasFiniteQuotients R]
    (d : R) (hd : d ≠ 0) :
    ((PrimeSpectrum.basicOpen d : Set (PrimeSpectrum R))ᶜ).Finite := by
  apply (Ring.HasFiniteQuotients.finite_setOfPred_mem d hd).of_injOn
    (f := PrimeSpectrum.asIdeal)
  · intro p hp
    simpa using hp
  · intro p _ q _ h
    exact PrimeSpectrum.ext h

/-- A closed subset of an arithmetic spectrum that misses its generic point
consists of finitely many primes. -/
theorem finite_closed_away_generic
    {R : Type*} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]
    (Z : Set (PrimeSpectrum R)) (hZ : IsClosed Z) (hη : ⊥ ∉ Z) : Z.Finite := by
  classical
  obtain ⟨s, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z).mp hZ
  obtain ⟨d, hd, hd0⟩ : ∃ d ∈ s, d ≠ 0 := by
    by_contra! h
    apply hη
    intro x hx
    exact h x hx
  apply (finite_complement_basicOpen d hd0).subset
  intro p hp
  simpa using hp hd

/-- A concrete localization subalgebra contains any prescribed finite
collection of coefficients. -/
theorem fg_subalgebra_le_localization
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (A : Subalgebra R K) (hA : A.FG) :
    ∃ (d : R) (_ : d ≠ 0) (hpow : Submonoid.powers d ≤ nonZeroDivisors R),
      A ≤ Localization.subalgebra.ofField K (Submonoid.powers d) hpow := by
  obtain ⟨d, hd, hle⟩ := fg_subalgebra_le_adjoin_inverse A hA
  have hpow : Submonoid.powers d ≤ nonZeroDivisors R := by
    rintro x ⟨n, rfl⟩
    exact pow_mem (mem_nonZeroDivisors_iff_ne_zero.mpr hd) n
  refine ⟨d, hd, hpow, hle.trans ?_⟩
  apply Algebra.adjoin_le
  rintro x (rfl : x = (algebraMap R K d)⁻¹)
  change ∃ (a s : R) (_ : s ∈ Submonoid.powers d),
    (algebraMap R K d)⁻¹ = algebraMap R K a * (algebraMap R K s)⁻¹
  exact ⟨1, d, Submonoid.mem_powers d, by simp⟩

/-- A smooth affine algebra over a fraction field spreads to a smooth
algebra over a localization at one nonzero denominator. -/
theorem smooth_algebra_model_over_localization
    {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (B : Type u) [CommRing B] [Algebra K B] [Algebra.Smooth K B] :
    ∃ (d : R) (_ : d ≠ 0) (hpow : Submonoid.powers d ≤ nonZeroDivisors R),
      let R₀ := Localization.subalgebra.ofField K (Submonoid.powers d) hpow
      ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra R₀ B₀),
        Algebra.Smooth R₀ B₀ ∧ Nonempty (B ≃ₐ[K] K ⊗[R₀] B₀) := by
  obtain ⟨A, C, hC, hAC, hA, hSmooth, ⟨e⟩⟩ :=
    Algebra.Smooth.exists_subalgebra_fg R K B
  let := hC
  let := hAC
  let := hSmooth
  obtain ⟨d, hd, hpow, hle⟩ := fg_subalgebra_le_localization A hA
  let R₀ := Localization.subalgebra.ofField K (Submonoid.powers d) hpow
  let : Algebra A R₀ := (Subalgebra.inclusion hle).toAlgebra
  let : IsScalarTower A R₀ K := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨d, hd, hpow, R₀ ⊗[A] C, inferInstance, inferInstance,
    inferInstance, ?_⟩
  exact ⟨e.trans (Algebra.TensorProduct.cancelBaseChange A R₀ K K C).symm⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.Fg.Construction
