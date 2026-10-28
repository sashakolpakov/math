import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine Neighborhood Open -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineNeighborhoodOpen.Construction.AffineNeighborhood

/-!
# Principal neighborhoods of finite subsets

Prime avoidance puts a finite collection of points of an affine scheme in a
single principal open contained in a prescribed open neighborhood.
-/

open _root_.TopologicalSpace _root_.AlgebraicGeometry

universe u

/-- A finite subset of an open in an affine spectrum lies in a principal
open contained in that open. -/
theorem exists_basicOpen
    {R : Type u} [CommRing R] (F : Set (PrimeSpectrum R)) (hF : F.Finite)
    (U : Opens (PrimeSpectrum R)) (hFU : F ⊆ U) :
    ∃ f : R, F ⊆ PrimeSpectrum.basicOpen f ∧ PrimeSpectrum.basicOpen f ≤ U := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨p₀, _⟩ := hne
    obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (U : Set (PrimeSpectrum R))ᶜ).mp
      U.isOpen.isClosed_compl
    have hn : ¬ (I : Set R) ⊆ ⋃ p ∈ F, (p.asIdeal : Set R) := by
      rw [Ideal.subset_union_prime_finite hF p₀ p₀ (fun p _ _ _ => p.isPrime)]
      rintro ⟨p, hp, hIp⟩
      have hz : p ∈ PrimeSpectrum.zeroLocus (I : Set R) := hIp
      rw [← hI] at hz
      exact hz (hFU hp)
    obtain ⟨f, hfI, hf⟩ := Set.not_subset.mp hn
    refine ⟨f, ?_, ?_⟩
    · intro p hp hfp
      exact hf (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hfp⟩⟩)
    · intro p hp
      by_contra hpu
      have hz : p ∈ PrimeSpectrum.zeroLocus (I : Set R) := hI ▸ hpu
      exact hp (hz hfI)
  · have hF0 : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact ⟨0, by simp [hF0], by simp⟩

/-- The same principal-neighborhood statement on an arbitrary affine scheme. -/
theorem exists_basicOpen_scheme (X : Scheme.{u}) [IsAffine X]
    (F : Set X) (hF : F.Finite) (U : X.Opens) (hFU : F ⊆ U) :
    ∃ f : Γ(X, ⊤), F ⊆ X.basicOpen f ∧ X.basicOpen f ≤ U := by
  obtain ⟨f, hfF, hfU⟩ := exists_basicOpen (X.isoSpec.hom '' F)
    (hF.image _) (X.isoSpec.inv ⁻¹ᵁ U) (by
      rintro _ ⟨x, hx, rfl⟩
      change X.isoSpec.inv (X.isoSpec.hom x) ∈ U
      simpa using hFU hx)
  refine ⟨f, ?_, ?_⟩
  · rw [← X.map_PrimeSpectrum_basicOpen_of_affine]
    intro x hx
    exact hfF ⟨x, hx, rfl⟩
  · rw [← X.map_PrimeSpectrum_basicOpen_of_affine]
    intro x hx
    have h := hfU hx
    change X.isoSpec.inv (X.isoSpec.hom x) ∈ U at h
    simpa using h

/-- A finite set already lying in one affine open has affine neighborhoods
inside any further prescribed open containing that set. -/
theorem exists_affineOpen_subset (X : Scheme.{u}) (F : Set X) (hF : F.Finite)
    (U V : X.Opens) (hU : IsAffineOpen U) (hFU : F ⊆ U) (hFV : F ⊆ V) :
    ∃ W : X.Opens, IsAffineOpen W ∧ F ⊆ W ∧ W ≤ U ∧ W ≤ V := by
  let : IsAffine U := hU
  have hF' : (U.ι ⁻¹' F).Finite := hF.preimage (f := U.ι) Subtype.val_injective.injOn
  obtain ⟨f, hfF, hfV⟩ := exists_basicOpen_scheme U.toScheme (U.ι ⁻¹' F) hF'
    (U.ι ⁻¹ᵁ V) (fun _ hx => hFV hx)
  refine ⟨U.ι ''ᵁ U.toScheme.basicOpen f,
    ((isAffineOpen_top U.toScheme).basicOpen f).image_of_isOpenImmersion U.ι,
    ?_, U.ι_image_le _, ?_⟩
  · intro x hx
    exact ⟨⟨x, hFU hx⟩, hfF hx, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    exact hfV hy

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineNeighborhoodOpen.Construction.AffineNeighborhood
