import OAI.AlgebraicGeometry.Quotients.FiniteDescent.InvariantPolynomialOf
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Determinant Cover Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DeterminantCoverEq.Construction.DeterminantCover

/-!
# Determinants of spanning families cover the spectrum

For a finite free module, the determinants of all tuples selected from a
spanning family generate the unit ideal. This gives the affine opens on which
target-valued tuples become bases in the finite-relation quotient construction.
-/

open _root_.Module
open scoped BigOperators

universe u v w z

variable {R : Type u} {M : Type v} {ι : Type w} {κ : Type z}
variable [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- Determinants of tuples from a spanning family generate the unit ideal. -/
theorem span_determinants_eq_top (b : Basis ι R M) (v : κ → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Ideal.span (Set.range (fun x : ι → κ => b.det (fun i => v (x i)))) = ⊤ := by
  classical
  let I : Ideal R := Ideal.span (Set.range (fun x : ι → κ => b.det (fun i => v (x i))))
  have hb (i : ι) : b i ∈ Submodule.span R (Set.range v) := by rw [hv]; trivial
  choose c hc using fun i => Finsupp.mem_span_range_iff_exists_finsupp.mp (hb i)
  have hc' (i : ι) : ∑ k ∈ (c i).support, c i k • v k = b i := hc i
  have hsum : b.det.toMultilinearMap
      (fun i => ∑ k ∈ (c i).support, c i k • v k) ∈ I := by
    rw [MultilinearMap.map_sum_finset]
    apply Submodule.sum_mem
    intro x _
    rw [MultilinearMap.map_smul_univ]
    apply Submodule.smul_mem
    exact Ideal.subset_span ⟨x, rfl⟩
  apply (Ideal.eq_top_iff_one _).mpr
  simp only [hc'] at hsum
  change b.det b ∈ I at hsum
  simpa only [Basis.det_self] using hsum

/-- At every proper ideal, some tuple from the spanning family has determinant
outside that ideal. -/
theorem exists_determinant_notMem (b : Basis ι R M) (v : κ → M)
    (hv : Submodule.span R (Set.range v) = ⊤) (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ x : ι → κ, b.det (fun i => v (x i)) ∉ I := by
  by_contra! h
  apply hI
  apply top_le_iff.mp
  rw [← span_determinants_eq_top b v hv]
  exact Ideal.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact h x)

variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D]
variable [Algebra A B] [Algebra B D]

/-- When target-valued elements span the relation algebra, their invariant
determinant denominators generate the unit ideal of the invariant ring. -/
theorem exists_invariant_cover
    (t : A →+* B) (ht : Function.Injective t) (p c : B →+* D)
    (hp : ∀ a, p (algebraMap A B a) = algebraMap B D (t a))
    (hc : ∀ a, c (algebraMap A B a) = algebraMap B D (algebraMap A B a))
    (hct : ∀ a, c (t a) = p (t a))
    (b : Basis ι A B) (dp dc : Basis ι B D)
    (hdp : ∀ i, dp i = p (b i)) (hdc : ∀ i, dc i = c (b i))
    (hspan : Submodule.span A (Set.range t) = ⊤) :
    ∃ g : (ι → A) → (algebraMap A B).eqLocus t,
      Ideal.span (Set.range g) = ⊤ ∧
      ∀ x, ∃ v : Aˣ,
        (g x : A) = (v : A) * (b.det (fun i => t (x i))) ^ Fintype.card ι := by
  classical
  let C := (algebraMap A B).eqLocus t
  let : Algebra C A := C.subtype.toAlgebra
  have hint : Algebra.IsIntegral C A :=
    ⟨InvariantPolynomialOf.Construction.InvariantPolynomial.integral_over_invariants t ht p c hp hc hct b dp dc hdp hdc⟩
  have hi : C.subtype.IsIntegral := algebraMap_isIntegral_iff.mpr hint
  choose g v hgv using
    InvariantPolynomialOf.Construction.InvariantPolynomial.exists_invariant_denominator t p c hp hc hct b dp dc hdp hdc
  refine ⟨g, ?_, fun x => ⟨v x, hgv x⟩⟩
  by_contra htop
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_le_maximal (Ideal.span (Set.range g)) htop
  obtain ⟨P, hP⟩ := hi.comap_surjective Subtype.val_injective ⟨J, hJ.isPrime⟩
  obtain ⟨x, hx⟩ := exists_determinant_notMem b t hspan P.asIdeal P.isPrime.ne_top
  have hgJ : g x ∈ J := hle (Ideal.subset_span ⟨x, rfl⟩)
  have hgP : (g x : A) ∈ P.asIdeal := by
    change g x ∈ (PrimeSpectrum.comap C.subtype P).asIdeal
    rw [hP]
    exact hgJ
  rw [hgv x] at hgP
  rcases P.isPrime.mem_or_mem hgP with hvP | hdP
  · exact Ideal.notMem_of_isUnit P.asIdeal (v x).isUnit hvP
  · exact hx (P.isPrime.mem_of_pow_mem _ hdP)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DeterminantCoverEq.Construction.DeterminantCover
