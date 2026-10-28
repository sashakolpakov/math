import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterPointedFrame

/-! # Center Finite Frame Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterFiniteFrameCover.Construction

noncomputable section

/-! Finite actual affine open covers carrying local coordinate frames of a curve center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- An actual affine open chart on which the original center is empty or
has a single coordinate equation with a dual derivation. -/
structure AffineCenterFrameChart (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (I : Ideal R) where
  carrier : CommRingCat.{u}
  algebra : Algebra k carrier
  map : R →ₐ[k] carrier
  isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom map.toRingHom))
  smooth : Algebra.Smooth k carrier
  center : I.map map.toRingHom = ⊤ ∨
    ∃ (g : carrier) (D : Derivation k carrier carrier), I.map map.toRingHom = Ideal.span {g} ∧ D g = 1

attribute [instance] AffineCenterFrameChart.algebra AffineCenterFrameChart.isOpenImmersion
  AffineCenterFrameChart.smooth

def AffineCenterFrameChart.openRange {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    {I : Ideal R} (C : AffineCenterFrameChart k R I) : TopologicalSpace.Opens (PrimeSpectrum R) :=
  (Spec.map (CommRingCat.ofHom C.map.toRingHom)).opensRange

variable (k : Type u) {R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R] [Algebra ℚ R] [IsNoetherianRing R]

theorem curve_center_frame_chart_at (hd : ringKrullDim R ≤ 1)
    (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤) (p : PrimeSpectrum R) :
    ∃ C : AffineCenterFrameChart k R I, p ∈ C.openRange := by
  classical
  by_cases hIp : I ≤ p.asIdeal
  · obtain ⟨S, aS, f, Q, hQ, hQp, hopen, hsmooth, g, D, hgen, hD⟩ :=
      CenterPointedFrame.Construction.curve_center_pointed_coordinate_neighborhood k hd I p.asIdeal hIp hI
    let C : AffineCenterFrameChart k R I :=
      ⟨S, aS, f, hopen, hsmooth, Or.inr ⟨g, D, hgen, hD⟩⟩
    refine ⟨C, ?_⟩
    change p ∈ Set.range (PrimeSpectrum.comap f.toRingHom)
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQp⟩
  · obtain ⟨a, haI, hap⟩ : ∃ a ∈ I, a ∉ p.asIdeal := by
      by_contra! h
      exact hIp h
    let S := Localization.Away a
    let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away a
    let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
    let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
    let C : AffineCenterFrameChart k R I :=
      ⟨.of S, inferInstance, f, IsOpenImmersion.of_isLocalization a, inferInstance,
        Or.inl (IdempotentQuotientCenter.Construction.center_map_away_member_eq_top I a haI)⟩
    have hdis : Disjoint (Submonoid.powers a : Set R) p.asIdeal :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime a).mpr hap
    have hQ := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers a) S
      p.asIdeal inferInstance hdis
    have hQp := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers a) S
      (I := p.asIdeal) inferInstance hdis
    refine ⟨C, ?_⟩
    change p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S))
    exact ⟨⟨p.asIdeal.map (algebraMap R S), hQ⟩, PrimeSpectrum.ext hQp⟩

/-- Quasi-compactness turns the actual coordinate neighborhoods into a
finite cover of the entire affine curve, including the complement of the center. -/
theorem exists_finite_curve_center_frame_cover (hd : ringKrullDim R ≤ 1)
    (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤) :
    ∃ (s : Finset (PrimeSpectrum R)) (C : s → AffineCenterFrameChart k R I),
      (⨆ i, (C i).openRange) = ⊤ := by
  classical
  choose C hC using curve_center_frame_chart_at k hd I hI
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

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterFiniteFrameCover.Construction
