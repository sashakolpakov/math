import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Exterior Basis Permutation -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorBasisPermutation.CM

noncomputable section

/-!
# Permuting exterior-basis lines

A permutation of a degree-one basis sends each exterior-basis vector to a
nonzero multiple of the vector indexed by the image subset. The proof uses
determinant coordinates and injectivity of the induced exterior map. It
does not assume that reordering wedge factors leaves a vector unchanged.
-/

open scoped Classical

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]
variable (n : ℕ) (b : Module.Basis ι K V) (π : Equiv.Perm ι)

/-- A permutation acts on finite subsets of a fixed cardinality. -/
def exteriorIndexPermutation : Equiv.Perm (Set.powersetCard ι n) where
  toFun := Set.powersetCard.map n π.toEmbedding
  invFun := Set.powersetCard.map n π.symm.toEmbedding
  left_inv s := by
    apply SetLike.coe_injective
    simp [Set.powersetCard.coe_map, Set.image_image]
  right_inv s := by
    apply SetLike.coe_injective
    simp [Set.powersetCard.coe_map, Set.image_image]

/-- Wedge a basis subset after applying a permutation to its indices. -/
def permutedExteriorVector (s : Set.powersetCard ι n) : ⋀[K]^n V :=
  exteriorPower.ιMulti K n (fun i => b (π (Set.powersetCard.ofFinEmbEquiv.symm s i)))

theorem permutedExteriorVector_eq_map (s : Set.powersetCard ι n) :
    permutedExteriorVector n b π s =
      exteriorPower.map n (b.equiv b π).toLinearMap (b.exteriorPower n s) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti K n)
  funext i
  simp only [Function.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply]

/-- Permuting independent wedge factors cannot annihilate their exterior product. -/
theorem permutedExteriorVector_ne_zero (s : Set.powersetCard ι n) :
    permutedExteriorVector n b π s ≠ 0 := by
  rw [permutedExteriorVector_eq_map]
  exact (map_ne_zero_iff _ (exteriorPower.map_injective_field (b.equiv b π).injective)).mpr
    ((b.exteriorPower n).ne_zero s)

/-- A permuted wedge has zero coordinates away from the permuted subset. -/
theorem permutedExteriorVector_coordinate_zero (s t : Set.powersetCard ι n)
    (hne : t ≠ exteriorIndexPermutation n π s) :
    (b.exteriorPower n).repr (permutedExteriorVector n b π s) t = 0 := by
  rw [exteriorPower.basis_repr_apply, permutedExteriorVector,
    exteriorPower.ιMultiDual_apply_ιMulti]
  obtain ⟨a, hat, han⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne t
    (exteriorIndexPermutation n π s)).mp hne
  obtain ⟨j, rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t a).mpr hat
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  have hi : π (Set.powersetCard.ofFinEmbEquiv.symm s i) ∈
      exteriorIndexPermutation n π s := by
    change π (Set.powersetCard.ofFinEmbEquiv.symm s i) ∈ Set.powersetCard.map n π.toEmbedding s
    rw [Set.powersetCard.mem_map_iff_mem_range]
    exact ⟨_, (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨i, rfl⟩, rfl⟩
  have hneq : Set.powersetCard.ofFinEmbEquiv.symm t j ≠
      π (Set.powersetCard.ofFinEmbEquiv.symm s i) := fun he => han (he ▸ hi)
  simp only [Matrix.of_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_of_ne hneq]

/-- The only remaining exterior coordinate is the multiplier of the image basis vector. -/
theorem permutedExteriorVector_eq_smul (s : Set.powersetCard ι n) :
    permutedExteriorVector n b π s =
      (b.exteriorPower n).repr (permutedExteriorVector n b π s)
        (exteriorIndexPermutation n π s) • b.exteriorPower n (exteriorIndexPermutation n π s) := by
  apply (b.exteriorPower n).ext_elem
  intro t
  by_cases ht : t = exteriorIndexPermutation n π s
  · subst t
    simp
  · rw [permutedExteriorVector_coordinate_zero n b π s t ht]
    simp [Ne.symm ht]

/-- Reordering only contributes a nonzero scalar on each exterior-basis line. -/
theorem permutedExteriorVector_coordinate_ne_zero (s : Set.powersetCard ι n) :
    (b.exteriorPower n).repr (permutedExteriorVector n b π s)
      (exteriorIndexPermutation n π s) ≠ 0 := by
  intro hz
  apply permutedExteriorVector_ne_zero n b π s
  rw [permutedExteriorVector_eq_smul n b π s, hz, zero_smul]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ExteriorBasisPermutation.CM
