import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenImmersionIsomorphism

/-! # Immersion Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.ImmersionPresentation

noncomputable section

/-! Every affine open immersion has a finite principal presentation by its actual localized maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_finite_principal_openImmersion_presentation
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))] :
    ∃ (k : ℕ) (f : Fin k → A),
      Ideal.span (Set.range (fun i => φ (f i))) = ⊤ ∧
      ∀ i, Function.Bijective (IsLocalization.Away.map
        (Localization.Away (f i)) (Localization.Away (φ (f i))) φ (f i)) := by
  classical
  have ho : IsOpen (Set.range (PrimeSpectrum.comap φ)) :=
    (Spec.map (CommRingCat.ofHom φ)).isOpenEmbedding.isOpen_range
  have hloc (x : PrimeSpectrum B) : ∃ a : A,
      PrimeSpectrum.comap φ x ∈ PrimeSpectrum.basicOpen a ∧
      (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) ⊆ Set.range (PrimeSpectrum.comap φ) := by
    obtain ⟨_, ⟨a, rfl⟩, hx, ha⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp ho _ ⟨x, rfl⟩
    exact ⟨a, hx, ha⟩
  choose a hx ha using hloc
  have hx' (x : PrimeSpectrum B) : x ∈ PrimeSpectrum.basicOpen (φ (a x)) := hx x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (PrimeSpectrum.basicOpen (φ (a x)) : Set (PrimeSpectrum B)))
    (fun x => (PrimeSpectrum.basicOpen (φ (a x))).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx' x⟩)
  let e := Fintype.equivFin t
  let f (i : Fin (Fintype.card t)) := a (e.symm i).val
  refine ⟨Fintype.card t, f, ?_, fun i =>
    Cartesian.OpenImmersionIsomorphism.localizationMap_bijective_of_basicOpen_subset_range φ (f i) (ha _)⟩
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro x
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨e ⟨y, hy⟩, ?_⟩
    have he : (e.symm (e ⟨y, hy⟩)).val = y := congrArg Subtype.val (e.symm_apply_apply ⟨y, hy⟩)
    exact (congrArg (fun z => x ∈ PrimeSpectrum.basicOpen (φ (a z))) he).mpr hxy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.ImmersionPresentation
