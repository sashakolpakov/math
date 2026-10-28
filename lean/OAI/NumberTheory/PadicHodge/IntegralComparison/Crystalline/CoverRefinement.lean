import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Refinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Covers

/-! # Cover Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoverRefinement

noncomputable section

/-!
# IntegralComparison: principal refinements of crystalline covering families

Every covering family in the big crystalline site admits a refinement by
principal crystalline opens. The defining functions are indexed by the
points of the ambient affine scheme and generate the unit ideal.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Refinement

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}

lemma principal_refinement {V : BigCrystallineSite.Object p B J δ f} (R : Presieve V) (hR : R ∈ BigCrystallineSite.Object.precoverage V) :
    ∃ r : PrimeSpectrum V.ring → V.ring, Ideal.span (Set.range r) = ⊤ ∧
      ∀ x, Sieve.generate R (Localization.hom V (r x)) := by
  classical
  obtain ⟨ι, W, β, rfl⟩ := R.exists_eq_ofArrows
  have hcover : (∀ x, ∃ i, x ∈ Set.range (BigCrystallineSite.Object.ambient.map (β i))) ∧
      ∀ i, IsOpenImmersion (BigCrystallineSite.Object.ambient.map (β i)) := by
    have h := hR.1
    rw [Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff] at h
    exact h
  have hc (i : ι) : BigCrystallineSite.Object.Cartesian (β i) := hR.2 (β i) (Presieve.ofArrows.mk i)
  have hlocal (x : PrimeSpectrum V.ring) : ∃ (i : ι) (r : V.ring),
      x ∈ PrimeSpectrum.basicOpen r ∧
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum V.ring)) ⊆ Set.range (BigCrystallineSite.Object.ambient.map (β i)) := by
    obtain ⟨i, hi⟩ := hcover.1 x
    have : IsOpenImmersion (BigCrystallineSite.Object.ambient.map (β i)) := hcover.2 i
    have hopen : IsOpen (Set.range (BigCrystallineSite.Object.ambient.map (β i))) :=
      (BigCrystallineSite.Object.ambient.map (β i)).isOpenEmbedding.isOpen_range
    obtain ⟨_, ⟨r, rfl⟩, hx, hr⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hi hopen
    exact ⟨i, r, hx, hr⟩
  choose i r hx hr using hlocal
  refine ⟨r, ?_, ?_⟩
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    have : IsOpenImmersion (BigCrystallineSite.Object.ambient.map (β (i x))) := hcover.2 (i x)
    rw [← CrystallinePrincipal.Refinement.factor_comp (β (i x)) (r x) (hc (i x)) (hr x)]
    exact (Sieve.generate (Presieve.ofArrows W β)).downward_closed
      (Sieve.ofArrows_mk W β (i x)) (CrystallinePrincipal.Refinement.factor (β (i x)) (r x) (hc (i x)) (hr x))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoverRefinement
