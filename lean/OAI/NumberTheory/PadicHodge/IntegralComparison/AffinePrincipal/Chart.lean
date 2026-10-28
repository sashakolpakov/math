import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover

/-! # Chart -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart

noncomputable section

/-! Actual principal localizations of an affine chart retain their map to the scheme and form arbitrarily small neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
  {X : Scheme.{u}} (g : Spec (CommRingCat.of A) ⟶ X) (r : A)

def map : Spec (CommRingCat.of (Localization.Away r)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))) ≫ g

instance map_open [IsOpenImmersion g] : IsOpenImmersion (Chart.map A g r) := by
  dsimp only [Chart.map]
  infer_instance

theorem localization_range :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))) =
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum A)) :=
  PrimeSpectrum.localization_away_comap_range (Localization.Away r) r

theorem lift (x : Spec (CommRingCat.of A)) (hx : r ∉ x.asIdeal) :
    ∃ y : Spec (CommRingCat.of (Localization.Away r)), Chart.map A g r y = g x := by
  have h : x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r)))) := by
    rw [localization_range]
    exact hx
  obtain ⟨y, hy⟩ := h
  exact ⟨y, congrArg g hy⟩

theorem over_base (f : X ⟶ Spec (CommRingCat.of k))
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    Chart.map A g r ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r))) := by
  change (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))) ≫ g) ≫ f = _
  rw [Category.assoc, hg, ← Spec.map_comp]
  congr 1

theorem neighborhood (U : X.Opens) (x : Spec (CommRingCat.of A)) (hx : g x ∈ U) :
    ∃ r : A, (∃ y : Spec (CommRingCat.of (Localization.Away r)), Chart.map A g r y = g x) ∧
      Set.range (Chart.map A g r) ⊆ U := by
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx (U.isOpen.preimage g.continuous)
  refine ⟨r, lift A g r x hr, ?_⟩
  rintro _ ⟨y, rfl⟩
  apply hsub
  have hm := congrArg (fun V : Set (PrimeSpectrum A) =>
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r))) y : PrimeSpectrum A) ∈ V)
    (localization_range A r)
  exact hm.mp ⟨y, rfl⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Chart
