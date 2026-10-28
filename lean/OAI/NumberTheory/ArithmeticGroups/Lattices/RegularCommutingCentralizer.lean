import OAI.NumberTheory.ArithmeticGroups.Lattices.RegularSelfAdjointCombination
import OAI.NumberTheory.ArithmeticGroups.Lattices.EndomorphismHilbertSchmidt

/-! # Regular Commuting Centralizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RegularCommutingCentralizer.Construction

noncomputable section

/-! A finite commuting family of self-adjoint operators has a real
linear combination with precisely the family's common centralizer. -/

open scoped Classical

theorem exists_regular_selfAdjoint_centralizer
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    [Fintype ι] (T : ι → L →L[ℝ] L) (hT : ∀ i, (T i).toLinearMap.IsSymmetric)
    (hcomm : Pairwise (fun i j => Commute (T i) (T j))) :
    ∃ c : ι → ℝ, ∀ X : L →L[ℝ] L, Commute (∑ i, c i • T i) X ↔ ∀ i, Commute (T i) X := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let b := stdOrthonormalBasis ℝ L
  let Φ := EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates b.toBasis
  let ρ := EndomorphismHilbertSchmidt.Construction.euclideanCommutatorRepresentation b
  have hsym (i : ι) : (ρ (T i)).toLinearMap.IsSymmetric :=
    EndomorphismHilbertSchmidt.Construction.euclideanCommutatorRepresentation_isSymmetric b (T i) (hT i)
  have hcomm' : Pairwise (fun i j => Commute (ρ (T i)).toLinearMap (ρ (T j)).toLinearMap) :=
    fun i j hij => EndomorphismHilbertSchmidt.Construction.euclideanCommutatorRepresentation_commute b (T i) (T j) (hcomm hij)
  obtain ⟨c, hc⟩ := RegularSelfAdjointCombination.Construction.exists_selfAdjoint_combination_common_kernel (fun i => (ρ (T i)).toLinearMap) hsym hcomm'
  have hsum : (∑ i, c i • (ρ (T i)).toLinearMap) = (ρ (∑ i, c i • T i)).toLinearMap := by
    rw [map_sum]
    simp only [map_smul, ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul]
  rw [hsum] at hc
  have hzero (A X : L →L[ℝ] L) : ρ A (Φ X) = 0 ↔ Commute A X := by
    rw [EndomorphismHilbertSchmidt.Construction.euclideanCommutatorRepresentation_apply]
    constructor
    · intro h
      have he : A * X - X * A = 0 := by
        apply Φ.injective
        simpa only [map_zero] using h
      exact sub_eq_zero.mp he
    · intro h
      rw [sub_eq_zero.mpr h.eq, map_zero]
  refine ⟨c, fun X => ?_⟩
  have he := congrArg (fun P : Submodule ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ L) × Fin (Module.finrank ℝ L))) =>
    Φ X ∈ P) hc
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at he
  have hiff := Iff.of_eq he
  change ρ (∑ i, c i • T i) (Φ X) = 0 ↔ ∀ i, ρ (T i) (Φ X) = 0 at hiff
  simpa only [hzero] using hiff

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RegularCommutingCentralizer.Construction
