import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ClosedTopology

/-! # Local Affine -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalAffine

noncomputable section

/-!
# IntegralComparison: principal neighborhoods with affine closed image

Every ambient point of a big crystalline object has a principal
neighborhood whose closed map lands in an affine open of X.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ClosedTopology

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
variable {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)}
variable (T : BigCrystallineSite.Object p B J δ f)

lemma exists_principal_affine (x : Spec (CommRingCat.of T.ring)) :
    ∃ (r : T.ring) (C : CommRingCat.{u}) (j : Spec C ⟶ X),
      IsOpenImmersion j ∧ r ∉ x.asIdeal ∧
        Set.range (Localization.object T r).mapToX ⊆ Set.range j := by
  obtain ⟨y, hy⟩ := ClosedTopology.quotientSpec_surjective T x
  obtain ⟨C, j, hj, z, hz⟩ := Scheme.exists_Spec_apply_eq (T.mapToX y)
  let : IsOpenImmersion j := hj
  have hm : y ∈ T.mapToX ⁻¹' Set.range j := ⟨z, hz⟩
  have hopen : IsOpen (T.mapToX ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage T.mapToX.continuous
  obtain ⟨_, ⟨c, rfl⟩, hc, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hm hopen
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨r, C, j, hj, ?_, ?_⟩
  · rw [← hy]
    change Ideal.Quotient.mk T.ideal r ∉ y.asIdeal
    rw [hr]
    exact hc
  · rintro _ ⟨w, rfl⟩
    apply hsub
    rw [← hr]
    exact ClosedTopology.closedMap_mem_basicOpen T r w

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.LocalAffine
