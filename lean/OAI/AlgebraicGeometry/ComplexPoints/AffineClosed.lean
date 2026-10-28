import OAI.AlgebraicGeometry.ComplexPoints.AffineDensity
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! # Affine Closed -/

namespace OAI.AlgebraicGeometry.ComplexPoints.AffineClosed.ClosednessConstruction

/-! Closedness: ordinary closedness detects Zariski closedness of locally closed sets. -/

open Set _root_.TopologicalSpace _root_.Topology

variable {B : Type*} [CommRing B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]

/-- A locally closed algebraic subset whose complex points are analytically
closed is Zariski closed. -/
theorem affine_locallyClosed_isClosed_of_analytic
    (S : Set (PrimeSpectrum B)) (hS : IsLocallyClosed S)
    (hA : IsClosed (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum ⁻¹' S)) : IsClosed S := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℂ B
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hS
  have hconstructible : IsConstructible (U ∩ Z) :=
    ((NoetherianSpace.isCompact U).isConstructible hU).inter
      (((NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl).of_compl)
  apply PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible
    ?_ hconstructible
  intro p q hpq hp
  have hqZ : q ∈ Z := hpq.mem_closed hZ hp.2
  have hle : p.asIdeal ≤ q.asIdeal := (PrimeSpectrum.le_iff_specializes p q).mpr hpq
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hU p hp.1
  let π : B →ₐ[ℂ] (B ⧸ p.asIdeal) := Ideal.Quotient.mkₐ ℂ p.asIdeal
  have hr : π r ≠ 0 := fun h =>
    hpr (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hdense := AffineDensity.ClosednessConstruction.dense_affine_principal_open (π r) hr
  have hclosed : IsClosed ((Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap π) ⁻¹' (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum ⁻¹' (U ∩ Z))) :=
    hA.preimage (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap π).continuous
  have hsub : {x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (B ⧸ p.asIdeal) | x (π r) ≠ 0} ⊆
      (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap π) ⁻¹' (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum ⁻¹' (U ∩ Z)) := by
    intro x hx
    refine ⟨hrU hx, ?_⟩
    have hpx : p ⤳ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap π x) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (by
        intro a ha
        change x (Ideal.Quotient.mk p.asIdeal a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])
    exact hpx.mem_closed hZ hp.2
  have hall (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (B ⧸ p.asIdeal)) :
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap π x) ∈ U ∩ Z :=
    (hclosed.closure_subset_iff.mpr hsub) (hdense x)
  by_contra hq
  have hqU : q ∉ U := fun h => hq ⟨h, hqZ⟩
  obtain ⟨M, hM, hqM⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
  let := hM
  obtain ⟨x, hx⟩ := IntegralCharacters.ClosednessConstruction.exists_character_of_maximal M
  have hpker : ∀ a ∈ p.asIdeal, x a = 0 := by
    intro a ha
    have hm : a ∈ RingHom.ker x.toRingHom := hx.symm ▸ hqM (hle ha)
    exact hm
  let xb : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (B ⧸ p.asIdeal) := Ideal.Quotient.liftₐ p.asIdeal x hpker
  have hxb : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap π xb = x := Ideal.Quotient.liftₐ_comp p.asIdeal x hpker
  have hxU : Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum x ∈ U := by
    rw [← hxb]
    exact (hall xb).1
  have hqx : q ⤳ Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum x :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (by
      change q.asIdeal ≤ RingHom.ker x.toRingHom
      rwa [hx])
  exact hqU (hqx.mem_open hU hxU)

end OAI.AlgebraicGeometry.ComplexPoints.AffineClosed.ClosednessConstruction
