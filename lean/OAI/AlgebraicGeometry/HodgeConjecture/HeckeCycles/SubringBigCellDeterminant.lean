import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot

/-! # Subring Big Cell Determinant -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SubringBigCellDeterminant.CM

noncomputable section

/-! Exact determinant comparison between an integral symplectic matrix
and its image in the ambient field, including inverse integrality. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.MatrixPivot.CM.SymplecticBigCell

variable {I K : Type*} [Fintype I] [CommRing K]

theorem determinant_map (S : Subring K) (g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I K) (hg : ∀ i j, g.val i j ∈ S)
    (B : Matrix I I S) :
    S.subtype (((Local.MatrixPivot.CM.SymplecticBigCell.subringSymplectic S g hg).val.toBlocks₁₁ +
      B * (Local.MatrixPivot.CM.SymplecticBigCell.subringSymplectic S g hg).val.toBlocks₂₁).det) =
      (g.val.toBlocks₁₁ + B.map S.subtype * g.val.toBlocks₂₁).det := by
  rw [RingHom.map_det, map_add, map_mul]
  rfl

theorem inverse_mem {K : Type*} [Field K] (S : Subring K) (x : S) (hx : IsUnit x) :
    (x.val)⁻¹ ∈ S := by
  obtain ⟨u, rfl⟩ := hx
  have he : ((u.val : S) : K)⁻¹ = (((u⁻¹).val : S) : K) := by
    exact (Units.val_inv_eq_inv_val (Units.map S.subtype.toMonoidHom u)).symm
  rw [he]
  exact (u⁻¹).val.property

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SubringBigCellDeterminant.CM
