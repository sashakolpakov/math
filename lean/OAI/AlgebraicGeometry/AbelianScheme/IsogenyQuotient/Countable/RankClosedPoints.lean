import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RankPoints
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Rank Closed Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RankClosedPoints.Construction

noncomputable section

/-! Every nonempty closed set in the spectrum of a countable-dimensional
algebra over an uncountable algebraically closed field contains a rational
point. Consequently open sets covering all rational points cover the spectrum. -/

variable (C R : Type) [Field C] [Uncountable C] [IsAlgClosed C]
    [CommRing R] [Algebra C R]

set_option backward.isDefEq.respectTransparency false in
theorem algHom_killing_ideal_of_countable_rank
    (h : Module.rank C R ≤ Cardinal.aleph0) (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ f : R →ₐ[C] C, I ≤ RingHom.ker f.toRingHom := by
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I hI
  let : J.IsMaximal := hJ
  let L := R ⧸ J
  let : Field L := Ideal.Quotient.field J
  have hr : Module.rank C L ≤ Module.rank C R :=
    (Ideal.Quotient.mkₐ C J).toLinearMap.rank_le_of_surjective (Ideal.Quotient.mk_surjective)
  have : Algebra.IsAlgebraic C L := RankPoints.Construction.field_isAlgebraic_of_countable_rank (C := C) (L := L) (hr.trans h)
  let e : C ≃ₐ[C] L := AlgEquiv.ofBijective (Algebra.ofId C L)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := C))
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C J), ?_⟩
  intro r hr
  change e.symm (Ideal.Quotient.mk J r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hr), map_zero]

def rationalKernelPoint (f : R →ₐ[C] C) : PrimeSpectrum R :=
  ⟨RingHom.ker f.toRingHom, RingHom.ker_isPrime f.toRingHom⟩

theorem closed_set_has_rational_point_of_countable_rank
    (h : Module.rank C R ≤ Cardinal.aleph0)
    (Z : Set (PrimeSpectrum R)) (hZ : IsClosed Z) (hNE : Z.Nonempty) :
    ∃ f : R →ₐ[C] C, rationalKernelPoint C R f ∈ Z := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  have hI : I ≠ ⊤ := by
    intro hI
    exact hNE.ne_empty (PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr hI)
  obtain ⟨f, hf⟩ := algHom_killing_ideal_of_countable_rank C R h I hI
  exact ⟨f, hf⟩

theorem open_set_eq_univ_of_rational_points
    (h : Module.rank C R ≤ Cardinal.aleph0)
    (U : Set (PrimeSpectrum R)) (hU : IsOpen U)
    (hpoints : ∀ f : R →ₐ[C] C, rationalKernelPoint C R f ∈ U) : U = Set.univ := by
  by_contra hne
  have hcomp : Uᶜ.Nonempty := Set.nonempty_compl.mpr hne
  obtain ⟨f, hf⟩ := closed_set_has_rational_point_of_countable_rank C R h Uᶜ hU.isClosed_compl hcomp
  exact hf (hpoints f)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.RankClosedPoints.Construction
