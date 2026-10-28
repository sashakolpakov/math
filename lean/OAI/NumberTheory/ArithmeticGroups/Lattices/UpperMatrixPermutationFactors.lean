import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationUnipotentFactors
import OAI.NumberTheory.ArithmeticGroups.Lattices.StrictOrderedUnipotentMatrices
import OAI.NumberTheory.ArithmeticGroups.Lattices.BasisSpectralOperator

/-! # Upper Matrix Permutation Factors -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UpperMatrixPermutationFactors.Construction

noncomputable section

/-! Continuous permutation factorization of the full upper
unitriangular matrix group. -/

open scoped Classical

theorem upper_matrix_continuous_permutation_factors (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    ∃ u v : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m → (Matrix (Fin m) (Fin m) ℝ)ˣ,
      Continuous u ∧ Continuous v ∧ ∀ g,
        UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (u g).val ∧ UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (v g).val ∧
        (∀ i j, ¬(i < j ∧ σ j < σ i) → ((u g).val - 1) i j = 0) ∧
        (∀ i j, ¬(i < j ∧ σ i < σ j) → ((v g).val - 1) i j = 0) ∧
        g.val = u g * v g := by
  let L := EuclideanSpace ℝ (Fin m)
  let b : OrthonormalBasis (Fin m) ℝ L := EuclideanSpace.basisFun (Fin m) ℝ
  let w : Fin m → ℝ := fun i => -(i.val : ℝ)
  have hw : StrictAnti w := by
    intro i j hij
    exact neg_lt_neg (Nat.cast_lt.mpr hij)
  let H : L →L[ℝ] L := (BasisSpectralOperator.Construction.basisSpectralEnd b.toBasis w).toContinuousLinearMap
  have hH : H.toLinearMap.IsSymmetric := BasisSpectralOperator.Construction.basisSpectralEnd_isSymmetric b w
  have heig : ∀ i, H (b i) = w i • b i := BasisSpectralOperator.Construction.basisSpectralEnd_apply_basis b.toBasis w
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis
  let e := StrictOrderedUnipotentMatrices.Construction.strictOrderedUnipotentMatrixEquiv b w hw
  obtain ⟨u, v, hu, hv, hf⟩ := PermutationUnipotentFactors.Construction.weightRaising_permutation_unipotent_factors b H hH w hw.antitone heig σ
  refine ⟨fun g => F (u (e.symm g)), fun g => F (v (e.symm g)),
    F.continuous.comp (hu.comp e.symm.continuous), F.continuous.comp (hv.comp e.symm.continuous), ?_⟩
  intro g
  obtain ⟨hug, hvg, hus, hvs, he⟩ := hf (e.symm g)
  refine ⟨StrictOrderedUnipotentMatrices.Construction.weightRaising_unit_matrix_upper b w hw.antitone ⟨_, hug⟩,
    StrictOrderedUnipotentMatrices.Construction.weightRaising_unit_matrix_upper b w hw.antitone ⟨_, hvg⟩, ?_, ?_, ?_⟩
  · intro i j hij
    have hz := hus i j hij
    simpa only [map_sub, map_one] using! hz
  · intro i j hij
    have hz := hvs i j hij
    simpa only [map_sub, map_one] using! hz
  · have heF := congrArg F he
    rw [map_mul] at heF
    have hg : F (e.symm g).val = g.val := by
      exact congrArg Subtype.val (e.apply_symm_apply g)
    rw [hg] at heF
    exact heF

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UpperMatrixPermutationFactors.Construction
