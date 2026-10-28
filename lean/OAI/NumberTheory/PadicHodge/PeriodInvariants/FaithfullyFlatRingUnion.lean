import OAI.NumberTheory.PadicHodge.PeriodInvariants.FlatUnion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Data.Fintype.Sets

/-! # Faithfully Flat Ring Union -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FaithfullyFlatRingUnion

noncomputable section

/-! # Embedded unions of faithfully flat algebras remain faithfully flat -/

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  (f : ∀ i, A i →ₐ[R] S) (hf : ∀ i, Function.Injective (f i))
  (hlift : ∀ s : Finset S, ∃ i, ∃ y : s → A i, ∀ j, f i (y j) = j.val)

include hf hlift

theorem flat [∀ i, Module.Flat R (A i)] : Module.Flat R S := by
  classical
  apply FlatUnion.flat A (fun i => (f i).toLinearMap) hf
  intro n x
  obtain ⟨i, y, hy⟩ := hlift (Finset.univ.image x)
  refine ⟨i, fun j => y ⟨x j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩, ?_⟩
  intro j
  exact hy _

theorem faithfullyFlat [∀ i, Module.FaithfullyFlat R (A i)] : Module.FaithfullyFlat R S := by
  classical
  have : Module.Flat R S := flat A f hf hlift
  apply (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top R S).mpr
  refine ⟨inferInstance, ?_⟩
  intro I hI
  have h₁ : (1 : S) ∈ I • (⊤ : Submodule R S) := by rw [hI]; trivial
  have hspan : (1 : S) ∈ I • Submodule.span R (Set.range (id : S → S)) := by
    simpa only [Set.range_id, Submodule.span_univ] using h₁
  obtain ⟨a, ha, he⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum I (id : S → S) 1).mp hspan
  obtain ⟨i, y, hy⟩ := hlift a.support
  have hs : ∑ j : a.support, a j.val • y j = (1 : A i) := by
    apply hf i
    rw [map_sum, map_one]
    simp only [map_smul, hy]
    change ∑ j ∈ a.support, a j • j = 1 at he
    rw [Finset.univ_eq_attach]
    exact (Finset.sum_attach a.support (fun j => a j • j)).trans he
  have hm : (1 : A i) ∈ I.map (algebraMap R (A i)) := by
    rw [← hs]
    apply (I.map (algebraMap R (A i))).sum_mem
    intro j _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha j.val))
  have hb : (1 : R) ∈ (I.map (algebraMap R (A i))).comap (algebraMap R (A i)) := by
    rw [Ideal.mem_comap, map_one]
    exact hm
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hb
  exact (Ideal.eq_top_iff_one I).mpr hb

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FaithfullyFlatRingUnion
