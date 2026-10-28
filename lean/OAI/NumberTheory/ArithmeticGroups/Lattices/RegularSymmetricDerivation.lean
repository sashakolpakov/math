import OAI.NumberTheory.ArithmeticGroups.Lattices.MaximalCommutingSubspace
import OAI.NumberTheory.ArithmeticGroups.Lattices.RegularCommutingCentralizer

/-! # Regular Symmetric Derivation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RegularSymmetricDerivation.Construction

noncomputable section

/-! A bracket has a maximal commuting subspace of symmetric
derivations and a regular element whose symmetric centralizer is that subspace. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

local instance symmetricDerivationEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance symmetricDerivationEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance symmetricDerivationEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

def symmetricDerivationSubmodule (B : L →L[ℝ] L →L[ℝ] L) : Submodule ℝ (L →L[ℝ] L) where
  carrier := {T | T.toLinearMap.IsSymmetric ∧ Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B T = 0}
  zero_mem' := ⟨by intro x y; simp, map_zero _⟩
  add_mem' hA hC := ⟨hA.1.add hC.1, by rw [map_add, hA.2, hC.2, add_zero]⟩
  smul_mem' c _ hA := ⟨LinearMap.IsSymmetric.smul (by simp) hA.1,
    by
      rw [map_smul, hA.2]
      ext x y
      exact smul_zero c⟩

theorem exists_regular_symmetric_derivation
    (B : L →L[ℝ] L →L[ℝ] L) :
    ∃ a : Submodule ℝ (L →L[ℝ] L), a ≤ symmetricDerivationSubmodule B ∧
      (∀ X ∈ a, ∀ Y ∈ a, Commute X Y) ∧
      ∃ H ∈ a, ∀ X ∈ symmetricDerivationSubmodule B, Commute H X ↔ X ∈ a := by
  obtain ⟨a, ha, hcomm, hmax⟩ := MaximalCommutingSubspace.Construction.exists_maximal_commuting_subspace (symmetricDerivationSubmodule B)
  let b := Module.finBasis ℝ a
  let T : Fin (Module.finrank ℝ a) → L →L[ℝ] L := fun i => (b i).val
  have hsym (i : Fin (Module.finrank ℝ a)) : (T i).toLinearMap.IsSymmetric := (ha (b i).property).1
  have hc : Pairwise (fun i j => Commute (T i) (T j)) :=
    fun i j _ => hcomm (b i).val (b i).property (b j).val (b j).property
  obtain ⟨c, hc⟩ := RegularCommutingCentralizer.Construction.exists_regular_selfAdjoint_centralizer T hsym hc
  let H := ∑ i, c i • T i
  have hH : H ∈ a := Submodule.sum_mem _ (fun i _ => a.smul_mem _ (b i).property)
  refine ⟨a, ha, hcomm, H, hH, fun X hX => ⟨fun hHX => ?_, fun hXa => hcomm H hH X hXa⟩⟩
  apply hmax X hX
  have hi : ∀ i, Commute (T i) X := (hc X).mp hHX
  let f : a →ₗ[ℝ] (L →L[ℝ] L) := (EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation X).toLinearMap.comp a.subtype
  have hf : f = 0 := by
    apply b.ext
    intro i
    change EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation X (T i) = 0
    rw [EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation_apply, sub_eq_zero.mpr (hi i).symm.eq]
  intro Y hY
  have he := DFunLike.congr_fun hf ⟨Y, hY⟩
  change EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation X Y = 0 at he
  rw [EndomorphismHilbertSchmidt.Construction.continuousCommutatorRepresentation_apply] at he
  exact sub_eq_zero.mp he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RegularSymmetricDerivation.Construction
