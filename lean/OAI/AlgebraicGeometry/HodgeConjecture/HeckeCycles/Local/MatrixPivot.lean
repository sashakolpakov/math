import OAI.LinearAlgebra.Symplectic.BigCell
import OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator

/-! # Matrix Pivot -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot.CM.SymplecticBigCell

/-! Local-ring symplectic reduction used to assemble an adelic big
cell. The lemma reuses the proved local-ring result in Mathlib. -/

open scoped Classical _root_.Matrix

variable {I K : Type*} [Fintype I] [CommRing K]

theorem exists_symmetric [IsLocalRing K] (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) :
    ∃ B : Matrix I I K, B.IsSymm ∧
      IsUnit (g.val.toBlocks₁₁ + B * g.val.toBlocks₂₁).det := by
  apply LinearAlgebra.Symplectic.BigCell.SymplecticBigCell.exists_symmetric_X_isUnit_det_add_mul_of_symplectic
  exact (show Matrix.fromBlocks g.val.toBlocks₁₁ g.val.toBlocks₁₂
    g.val.toBlocks₂₁ g.val.toBlocks₂₂ ∈ Matrix.symplecticGroup I K from by
      simpa only [Matrix.fromBlocks_toBlocks] using g.property)

def subringMatrix (S : Subring K) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) (hg : ∀ i j, g.val i j ∈ S) :
    Matrix (I ⊕ I) (I ⊕ I) S := fun i j => ⟨g.val i j, hg i j⟩

theorem subringMatrix_map (S : Subring K) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) (hg : ∀ i j, g.val i j ∈ S) :
    (subringMatrix S g hg).map S.subtype = g.val := rfl

theorem subringMatrix_symplectic (S : Subring K) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) (hg : ∀ i j, g.val i j ∈ S) :
    subringMatrix S g hg ∈ Matrix.symplecticGroup I S := by
  apply SymplecticGroup.mem_iff'.mpr
  apply Matrix.map_injective S.subtype_injective
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_J, subringMatrix_map]
  exact SymplecticGroup.mem_iff'.mp g.property

def subringSymplectic (S : Subring K) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) (hg : ∀ i j, g.val i j ∈ S) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I S :=
  ⟨subringMatrix S g hg, subringMatrix_symplectic S g hg⟩

theorem subringSymplectic_map (S : Subring K) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) (hg : ∀ i j, g.val i j ∈ S) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp S.subtype (subringSymplectic S g hg) = g := Subtype.ext rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot.CM.SymplecticBigCell

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot.CM

/-! An invertible matrix over a local ring has a unit in each column.
Adding at most one other row makes a chosen diagonal entry a unit.
The correction coefficients are all zero or one. -/

open scoped Classical _root_.Matrix

variable {I R : Type*} [Fintype I] [CommRing R] [IsLocalRing R]

theorem column_unit (A : (Matrix I I R)ˣ) (i : I) : ∃ j, IsUnit (A.val j i) := by
  have he := congrArg (fun M : Matrix I I R => M i i) A.inv_val
  simp only [Matrix.mul_apply, Matrix.one_apply, ite_true] at he
  change (∑ j, (A⁻¹).val i j * A.val j i) = 1 at he
  have hu : IsUnit (∑ j, (A⁻¹).val i j * A.val j i) := he.symm ▸ isUnit_one
  obtain ⟨j, _, hj⟩ := IsLocalRing.exists_of_isUnit_sum hu
  exact ⟨j, (IsUnit.mul_iff.mp hj).2⟩

theorem nonunit_add_unit {a b : R} (ha : ¬ IsUnit a) (hb : IsUnit b) : IsUnit (a + b) := by
  by_contra hab
  have hn : ¬ IsUnit (-a) := fun h => ha (by simpa only [neg_neg] using h.neg)
  have hh := IsLocalRing.nonunits_add hab hn
  have he : a + b + -a = b := by ring
  rw [he] at hh
  exact hh hb

theorem exists_binary_correction (A : (Matrix I I R)ˣ) (i : I) :
    ∃ c : I → R, c i = 0 ∧ (∀ j, c j = 0 ∨ c j = 1) ∧
      IsUnit (A.val i i + ∑ j, c j * A.val j i) := by
  by_cases hii : IsUnit (A.val i i)
  · refine ⟨0, rfl, fun _ => Or.inl rfl, ?_⟩
    simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using hii
  · obtain ⟨j, hj⟩ := column_unit A i
    have hji : j ≠ i := by rintro rfl; exact hii hj
    refine ⟨Pi.single j 1, ?_, ?_, ?_⟩
    · simp [Ne.symm hji]
    · intro k
      by_cases hk : k = j <;> simp [hk]
    · simpa [Pi.single_apply] using nonunit_add_unit hii hj

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot.CM

end

end OAI
