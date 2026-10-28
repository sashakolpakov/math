import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentLifts
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! # Finite Local Extension -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteLocalExtension.Lifts

noncomputable section

/-!
A finite domain over a henselian local ring is local. HenselianLifting lifts the
residue idempotents, and the domain has no nontrivial idempotents.
This supplies locality of the integral closure in an evaluation field.
-/

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ComponentLifts.Components

variable (R A : Type u) [CommRing R] [HenselianLocalRing R]
variable [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A]

theorem finite_domain_residue_idempotent (e : ComponentLifts.Components.ResidueAlgebra R A)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  let a := ComponentLifts.Components.liftIdempotent R A e he
  have ha : IsIdempotentElem a := ComponentLifts.Components.liftIdempotent_idem R A e he
  have hr := ComponentLifts.Components.liftIdempotent_reduction R A e he
  change Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R A)) a = e at hr
  have hzero : a * (1 - a) = 0 := isIdempotentElem_iff_mul_one_sub_self.mp ha
  rcases mul_eq_zero.mp hzero with h | h
  · left
    simpa only [show a = 0 from h, map_zero] using hr.symm
  · right
    have h' : a = 1 := (sub_eq_zero.mp h).symm
    simpa only [show a = 1 from h', map_one] using hr.symm

theorem finite_domain_residue_spectrum_subsingleton :
    Subsingleton (PrimeSpectrum (ComponentLifts.Components.ResidueAlgebra R A)) := by
  let k := IsLocalRing.ResidueField R
  let Q := ComponentLifts.Components.ResidueAlgebra R A
  let : Algebra k Q := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R k Q := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite k Q := Module.Finite.of_restrictScalars_finite R k Q
  have : IsArtinianRing Q := isArtinian_of_tower k inferInstance
  constructor
  intro x y
  obtain ⟨e, he, hopen⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen
    (isClopen_discrete ({x} : Set (PrimeSpectrum Q)))
  rcases finite_domain_residue_idempotent R A e he with rfl | rfl
  · have hx : x ∈ (PrimeSpectrum.basicOpen (0 : Q) : Set (PrimeSpectrum Q)) := by
      rw [← hopen]
      exact Set.mem_singleton x
    simp at hx
  · have hy : y ∈ ({x} : Set (PrimeSpectrum Q)) := by
      rw [hopen]
      simp
    exact (Set.mem_singleton_iff.mp hy).symm

include R in
/-- Locality of the finite integral domain is derived, so the finite
evaluation extension need not be supplied with a chosen local factor. -/
theorem finite_domain_isLocalRing : IsLocalRing A := by
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  let φ := Ideal.Quotient.mk I
  have hker (m : Ideal A) (hm : m.IsMaximal) : RingHom.ker φ ≤ m := by
    rw [show RingHom.ker φ = I from Ideal.mk_ker]
    exact (OAI.Algebra.LocalRing.HenselianLifting.Construction.maximalIdeal_map_le_jacobson R A).trans (sInf_le ⟨bot_le, hm⟩)
  have : Subsingleton (PrimeSpectrum (A ⧸ I)) := finite_domain_residue_spectrum_subsingleton R A
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  refine IsLocalRing.of_unique_max_ideal ⟨m, hm, ?_⟩
  intro n hn
  have : m.IsMaximal := hm
  have : n.IsMaximal := hn
  have : (m.map φ).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker m hm)
  have : (n.map φ).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hker n hn)
  have he : n.map φ = m.map φ := congrArg PrimeSpectrum.asIdeal
    (Subsingleton.elim (⟨n.map φ, inferInstance⟩ : PrimeSpectrum (A ⧸ I)) ⟨m.map φ, inferInstance⟩)
  have hc := congrArg (Ideal.comap φ) he
  simpa only [Ideal.comap_map_of_surjective φ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr (hker n hn), sup_eq_left.mpr (hker m hm)] using hc

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FiniteLocalExtension.Lifts
