import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover

/-! # Projection Neighborhoods -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ProjectionNeighborhoods

noncomputable section

/-! Principal neighborhoods in a factor can be chosen over every point of a crystalline product lying in a fixed chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ClosedTopology

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  {T U : BigCrystallineSite.Object p B J δ f} (α : T ⟶ U) {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
  (hα : Set.range T.mapToX ⊆ Set.range j)

include hα in
theorem neighborhood (z : Spec (CommRingCat.of T.ring)) :
    ∃ r : U.ring, α.ringMap r ∉ z.asIdeal ∧ Set.range (Localization.object U r).mapToX ⊆ Set.range j := by
  obtain ⟨y, hy⟩ := ClosedTopology.quotientSpec_surjective T z
  have hi : U.mapToX (BigCrystallineSite.Object.closed.map α y) ∈ Set.range j := by
    have he := congrArg (fun g => g y) α.overX
    exact he.symm ▸ hα ⟨y, rfl⟩
  have hopen : IsOpen (U.mapToX ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage U.mapToX.continuous
  obtain ⟨_, ⟨c, rfl⟩, hc, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi hopen
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨r, ?_, ?_⟩
  · rw [← hy]
    change BigCrystallineSite.Object.quotientMap T U α.ringMap c ∉ y.asIdeal at hc
    rw [← hr] at hc
    exact hc
  · rintro _ ⟨w, rfl⟩
    apply hsub
    rw [← hr]
    exact ClosedTopology.closedMap_mem_basicOpen U r w

include hα in
theorem finite_cover : ∃ s : Finset T.ring, Ideal.span (s : Set T.ring) = ⊤ ∧
    ∀ a ∈ s, ∃ r : U.ring, a = α.ringMap r ∧ Set.range (Localization.object U r).mapToX ⊆ Set.range j := by
  obtain ⟨s, hs, hspan⟩ := Principal.OpenCover.finite_unit_family
    (fun a : T.ring => ∃ r : U.ring, a = α.ringMap r ∧ Set.range (Localization.object U r).mapToX ⊆ Set.range j) (by
      intro z
      obtain ⟨r, hr, hsub⟩ := neighborhood α j hα z
      exact ⟨α.ringMap r, ⟨r, rfl, hsub⟩, hr⟩)
  exact ⟨s, hspan, hs⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ProjectionNeighborhoods
