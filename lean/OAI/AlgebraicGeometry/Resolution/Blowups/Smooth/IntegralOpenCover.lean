import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.Neighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Integral Open Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.IntegralOpenCover.Construction

noncomputable section

/-! Finite actual integral affine open covers of smooth algebras. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

structure IntegralAffineOpenChart (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] where
  carrier : CommRingCat.{u}
  algebra : Algebra k carrier
  map : R →ₐ[k] carrier
  isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom map.toRingHom))
  smooth : Algebra.Smooth k carrier
  domain : IsDomain carrier

attribute [instance] IntegralAffineOpenChart.algebra IntegralAffineOpenChart.isOpenImmersion
  IntegralAffineOpenChart.smooth IntegralAffineOpenChart.domain

def IntegralAffineOpenChart.openRange {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (C : IntegralAffineOpenChart k R) : TopologicalSpace.Opens (PrimeSpectrum R) :=
  (Spec.map (CommRingCat.ofHom C.map.toRingHom)).opensRange

variable (k : Type u) {R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]

/-- Every closed point of a smooth affine scheme lies in an actual
integral smooth affine open chart over the original ground field. -/
theorem smooth_integral_open_chart_at_closed_point (q : Ideal R) [q.IsMaximal] :
    ∃ C : IntegralAffineOpenChart k R, (⟨q, inferInstance⟩ : PrimeSpectrum R) ∈ C.openRange := by
  obtain ⟨s, hs, d, pAlg, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := q)
  let A := Localization.Away s
  let : Algebra (MvPolynomial (Fin d) k) A := pAlg
  let : IsScalarTower k (MvPolynomial (Fin d) k) A := ht
  let : Algebra.IsStandardEtale (MvPolynomial (Fin d) k) A := he
  have hproper : q.map (algebraMap R A) ≠ ⊤ :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint (Submonoid.powers s) A q).mpr
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs)
  obtain ⟨Q, hQmax, hQle⟩ := Ideal.exists_le_maximal (q.map (algebraMap R A)) hproper
  let : Q.IsMaximal := hQmax
  have hQA : Q.comap (algebraMap R A) = q := by
    have hp : (Q.comap (algebraMap R A)).IsPrime := inferInstance
    exact ((inferInstance : q.IsMaximal).eq_of_le hp.ne_top (Ideal.le_comap_of_map_le hQle)).symm
  obtain ⟨t, htQ, _, hdomain⟩ := Integral.Neighborhood.Construction.exists_integral_etale_principal_neighborhood
    (σ := Fin d) (k := k) Q
  let S := Localization.Away t
  let : Algebra.Smooth R A := Algebra.Smooth.of_isLocalization_Away s
  let : Algebra.Smooth k A := Algebra.Smooth.comp k R A
  let : Algebra.Smooth A S := Algebra.Smooth.of_isLocalization_Away t
  let : Algebra.Smooth k S := Algebra.Smooth.comp k A S
  let f : R →ₐ[k] S := (IsScalarTower.toAlgHom k A S).comp (IsScalarTower.toAlgHom k R A)
  have hopen : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
      IsOpenImmersion.of_isLocalization s
    let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A S))) :=
      IsOpenImmersion.of_isLocalization t
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R A) ≫
      CommRingCat.ofHom (algebraMap A S)))
    rw [Spec.map_comp]
    infer_instance
  let C : IntegralAffineOpenChart k R := ⟨.of S, inferInstance, f, hopen, inferInstance, hdomain⟩
  obtain ⟨P, hP⟩ := Etale.RefinementHelpers.Construction.exists_localization_away_prime t (⟨Q, inferInstance⟩ : PrimeSpectrum A) htQ
  refine ⟨C, ?_⟩
  change (⟨q, inferInstance⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap f.toRingHom)
  refine ⟨P, PrimeSpectrum.ext ?_⟩
  change P.asIdeal.comap ((algebraMap A S).comp (algebraMap R A)) = q
  have hPI : P.asIdeal.comap (algebraMap A S) = Q := congrArg PrimeSpectrum.asIdeal hP
  rw [← Ideal.comap_comap, hPI, hQA]

/-- The same actual integral charts cover every prime: an open containing
a maximal specialization also contains the original prime. -/
theorem smooth_integral_open_chart_at (p : PrimeSpectrum R) :
    ∃ C : IntegralAffineOpenChart k R, p ∈ C.openRange := by
  obtain ⟨q, hq, hpq⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let : q.IsMaximal := hq
  obtain ⟨C, hC⟩ := smooth_integral_open_chart_at_closed_point k q
  exact ⟨C, ((PrimeSpectrum.le_iff_specializes p ⟨q, inferInstance⟩).mp hpq).mem_open C.openRange.isOpen hC⟩

/-- A finite actual integral smooth affine open cover exists without any
connectedness or integrality hypothesis on the original smooth algebra. -/
theorem exists_finite_smooth_integral_open_cover :
    ∃ (s : Finset (PrimeSpectrum R)) (C : s → IntegralAffineOpenChart k R),
      (⨆ i, (C i).openRange) = ⊤ := by
  classical
  choose C hC using smooth_integral_open_chart_at k (R := R)
  have hcover : Set.univ ⊆ ⋃ p, ((C p).openRange : Set (PrimeSpectrum R)) := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p, hC p⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun p => ((C p).openRange : Set (PrimeSpectrum R))) (fun p => (C p).openRange.isOpen) hcover
  refine ⟨s, fun p => C p.val, top_le_iff.mp ?_⟩
  intro p _
  obtain ⟨i, hi, hp⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ p))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.IntegralOpenCover.Construction
