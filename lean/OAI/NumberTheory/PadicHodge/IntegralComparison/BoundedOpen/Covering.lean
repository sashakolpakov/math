import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Support
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PrincipalCovers

/-! # Covering -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Covering

noncomputable section

/-!
# IntegralComparison: geometric open covers cover the original bounded crystalline site
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Support OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ClosedTopology

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of B)} {n : ℕ}
  {ι : Type u} (V : ι → Y.Opens)

def sieve (T : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n) : Sieve T where
  arrows U _ := ∃ i, SectionPresheaf.property fY n (V i) U
  downward_closed := by
    intro U W α h β
    obtain ⟨i, hi⟩ := h
    exact ⟨i, SectionPresheaf.incoming fY n (V i) β hi⟩

variable (T : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)
  (hcover : ∀ z : Spec (CommRingCat.of (T.obj.ring ⧸ T.obj.ideal)), ∃ i, T.obj.mapToX z ∈ V i)

include hcover in
theorem principal_neighborhood (z : Spec T.obj.ring) :
    ∃ (r : T.obj.ring) (i : ι), r ∉ z.asIdeal ∧
      SectionPresheaf.property fY n (V i) (Bounded.PrincipalCovers.object T r) := by
  obtain ⟨y, hy⟩ := Crystalline.ClosedTopology.quotientSpec_surjective T.obj z
  obtain ⟨i, hi⟩ := hcover y
  have hopen : IsOpen (T.obj.mapToX ⁻¹' (V i : Set Y)) :=
    (V i).isOpen.preimage T.obj.mapToX.continuous
  obtain ⟨_, ⟨c, rfl⟩, hc, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi hopen
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨r, i, ?_, (Support.property_iff_range_subset fY n _ (V i)).mpr ?_⟩
  · rw [← hy]
    change Ideal.Quotient.mk T.obj.ideal r ∉ y.asIdeal
    rw [hr]
    exact hc
  · rintro _ ⟨w, rfl⟩
    apply hsub
    rw [← hr]
    exact Crystalline.ClosedTopology.closedMap_mem_basicOpen T.obj r w

include hcover in
theorem finite_principal_refinement :
    ∃ s : Finset T.obj.ring, Ideal.span (s : Set T.obj.ring) = ⊤ ∧
      ∀ r ∈ s, ∃ i, SectionPresheaf.property fY n (V i) (Bounded.PrincipalCovers.object T r) := by
  obtain ⟨s, hs, hspan⟩ := Principal.OpenCover.finite_unit_family
    (fun r : T.obj.ring => ∃ i, SectionPresheaf.property fY n (V i) (Bounded.PrincipalCovers.object T r)) (by
      intro z
      obtain ⟨r, i, hr, hi⟩ := principal_neighborhood V T hcover z
      exact ⟨r, ⟨i, hi⟩, hr⟩)
  exact ⟨s, hspan, hs⟩

include hcover in
theorem covering : sieve V T ∈ BoundedCrystalline.Site.topology fY n T := by
  obtain ⟨s, hspan, hs⟩ := finite_principal_refinement V T hcover
  have he : Set.range (fun r : s => r.val) = (s : Set T.obj.ring) := by
    ext a
    exact ⟨fun ⟨b, hb⟩ => hb ▸ b.property, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
  have hcover' := Bounded.PrincipalCovers.coveringSieve T (fun r : s => r.val)
    (he ▸ hspan)
  apply (BoundedCrystalline.Site.topology fY n).superset_covering _ hcover'
  apply (Sieve.generate_le_iff _ _).mpr
  intro U α hα
  cases hα with
  | mk r => exact hs r.val r.property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Covering
