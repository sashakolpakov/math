import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ClosedTopology
import Mathlib.RingTheory.Ideal.Maximal

/-! # Open Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover

noncomputable section

/-!
# IntegralComparison: finite principal refinements subordinate to a fixed open cover

A crystalline thickening's closed subscheme has the same points as its
ambient scheme. Pulling back a fixed open cover and refining by principal
opens therefore gives principal neighborhoods at every ambient point.
The unit-ideal argument extracts finitely many such neighborhoods.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ClosedTopology

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
  (T : BigCrystallineSite.Object p B J δ f)
  {ι : Type u} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  (hcover : ∀ z : X, ∃ i, z ∈ Set.range (j i))

include hcover in
theorem principal_neighborhood (z : Spec (CommRingCat.of T.ring)) :
    ∃ (r : T.ring) (i : ι), r ∉ z.asIdeal ∧
      Set.range (Crystalline.Localization.object T r).mapToX ⊆ Set.range (j i) := by
  obtain ⟨y, hy⟩ := Crystalline.ClosedTopology.quotientSpec_surjective T z
  obtain ⟨i, hi⟩ := hcover (T.mapToX y)
  have hopen : IsOpen (T.mapToX ⁻¹' Set.range (j i)) :=
    (j i).isOpenEmbedding.isOpen_range.preimage T.mapToX.continuous
  obtain ⟨_, ⟨c, rfl⟩, hc, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi hopen
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨r, i, ?_, ?_⟩
  · rw [← hy]
    change Ideal.Quotient.mk T.ideal r ∉ y.asIdeal
    rw [hr]
    exact hc
  · rintro _ ⟨w, rfl⟩
    apply hsub
    rw [← hr]
    exact Crystalline.ClosedTopology.closedMap_mem_basicOpen T r w

/-- Pointwise principal neighborhoods admit a finite unit-generating subfamily. -/
theorem finite_unit_family {R : Type u} [CommRing R] (P : R → Prop)
    (hP : ∀ z : PrimeSpectrum R, ∃ r, P r ∧ r ∉ z.asIdeal) :
    ∃ s : Finset R, (∀ r ∈ s, P r) ∧ Ideal.span (s : Set R) = ⊤ := by
  have hspan : Ideal.span {r : R | P r} = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    let : M.IsMaximal := hM
    obtain ⟨r, hr, hnot⟩ := hP ⟨M, inferInstance⟩
    exact hnot (hle (Ideal.subset_span hr))
  have h1 : (1 : R) ∈ Ideal.span {r : R | P r} := by rw [hspan]; trivial
  obtain ⟨s, hs, h1s⟩ := Submodule.mem_span_finite_of_mem_span h1
  exact ⟨s, fun r hr => hs hr, (Ideal.eq_top_iff_one _).mpr h1s⟩

include hcover in
theorem finite_principal_refinement :
    ∃ s : Finset T.ring, Ideal.span (s : Set T.ring) = ⊤ ∧
      ∀ r ∈ s, ∃ i, Set.range (Crystalline.Localization.object T r).mapToX ⊆ Set.range (j i) := by
  obtain ⟨s, hs, hspan⟩ := finite_unit_family
    (fun r : T.ring => ∃ i, Set.range (Crystalline.Localization.object T r).mapToX ⊆ Set.range (j i)) (by
      intro z
      obtain ⟨r, i, hr, hi⟩ := principal_neighborhood T Y j hcover z
      exact ⟨r, ⟨i, hi⟩, hr⟩)
  exact ⟨s, hspan, hs⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover
