import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Norm Open Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormOpenIs.Construction.NormOpen

/-!
# The open defined by a finite-free norm

The norm of an element does not vanish at a prime exactly when the element
does not vanish at any prime above it. This identifies the complement of a
finite image of a principal closed set with a principal open.
-/

open TensorProduct

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

theorem isUnit_norm_iff [Module.Free R A] [Module.Finite R A] (a : A) :
    IsUnit (Algebra.norm R a) ↔ IsUnit a := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det, Algebra.lmul_isUnit_iff]

theorem norm_baseChange [Module.Free R A] [Module.Finite R A]
    (S : Type*) [CommRing S] [Algebra R S] (a : A) :
    Algebra.norm S (1 ⊗ₜ[R] a : S ⊗[R] A) = algebraMap R S (Algebra.norm R a) := by
  rw [Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange,
    Algebra.norm_apply]

/-- An element is a unit in a residue-field fiber precisely when it avoids
all the primes of the original algebra lying over that point. -/
theorem isUnit_fiber_iff (p : PrimeSpectrum R) (a : A) :
    IsUnit (1 ⊗ₜ[R] a : p.asIdeal.ResidueField ⊗[R] A) ↔
      ∀ q : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap R A) q = p → a ∉ q.asIdeal := by
  constructor
  · intro h q hq
    subst p
    let F : (q.asIdeal.comap (algebraMap R A)).ResidueField ⊗[R] A →ₐ[R]
        q.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift (Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) rfl)
        (IsScalarTower.toAlgHom _ _ _) (fun _ _ => Commute.all ..)
    have hu : IsUnit (algebraMap A q.asIdeal.ResidueField a) := by
      have hF := h.map F
      change IsUnit (F (1 ⊗ₜ[R] a)) at hF
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul] at hF
      exact hF
    intro ha
    exact hu.ne_zero (Ideal.algebraMap_residueField_eq_zero.mpr ha)
  · intro h
    by_contra hn
    obtain ⟨m, hm, ha⟩ := exists_max_ideal_of_mem_nonunits hn
    let q : PrimeSpectrum A :=
      PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom ⟨m, hm.isPrime⟩
    have hq : PrimeSpectrum.comap (algebraMap R A) q = p := by
      dsimp only [q]
      rw [← PrimeSpectrum.comap_comp_apply,
        ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
        PrimeSpectrum.comap_comp_apply]
      apply Set.mem_singleton_iff.mp
      rw [← PrimeSpectrum.residueField_comap p]
      exact Set.mem_range_self _
    exact h q hq ha

/-- Norm nonvanishing means nonvanishing at every point of the fiber. -/
theorem norm_notMem_iff [Module.Free R A] [Module.Finite R A]
    (p : PrimeSpectrum R) (a : A) :
    Algebra.norm R a ∉ p.asIdeal ↔
      ∀ q : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap R A) q = p → a ∉ q.asIdeal := by
  rw [← isUnit_fiber_iff, ← isUnit_norm_iff (R := p.asIdeal.ResidueField),
    norm_baseChange, isUnit_iff_ne_zero]
  exact not_congr Ideal.algebraMap_residueField_eq_zero.symm

theorem basicOpen_norm [Module.Free R A] [Module.Finite R A] (a : A) :
    (PrimeSpectrum.basicOpen (Algebra.norm R a) : Set (PrimeSpectrum R)) =
      (PrimeSpectrum.comap (algebraMap R A) '' PrimeSpectrum.zeroLocus {a})ᶜ := by
  ext p
  change Algebra.norm R a ∉ p.asIdeal ↔ _
  rw [norm_notMem_iff]
  simp only [Set.mem_compl_iff, Set.mem_image, PrimeSpectrum.mem_zeroLocus,
    Set.singleton_subset_iff, SetLike.mem_coe, not_exists, not_and]
  exact ⟨fun h q ha hq => h q hq ha, fun h q hq ha => h q ha hq⟩

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.NormOpenIs.Construction.NormOpen
