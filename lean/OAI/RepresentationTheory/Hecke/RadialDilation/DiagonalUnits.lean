import OAI.RepresentationTheory.Hecke.RadialDilation.PositionReindex
import OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice

/-! # Diagonal Units -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.DiagonalUnits.Realization

noncomputable section

/-! Diagonal units and the determinant of a selected three-coordinate dilation. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

def diagonalUnitMatrix {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (a : I → Kˣ) : Matrix.GeneralLinearGroup I K where
  val := Matrix.diagonal (fun i => (a i : K))
  inv := Matrix.diagonal (fun i => ((a i)⁻¹ : Kˣ).val)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.mul_inv, Matrix.diagonal_one]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [Units.inv_mul, Matrix.diagonal_one]

theorem diagonalUnitMatrix_det {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (a : I → Kˣ) : Matrix.GeneralLinearGroup.det (diagonalUnitMatrix a) = ∏ i, a i := by
  apply Units.ext
  change (Matrix.diagonal (fun i => (a i : K))).det = _
  rw [Matrix.det_diagonal]
  exact (map_prod (Units.coeHom K) a Finset.univ).symm

theorem diagonalUnitMatrix_inverse_action {I K : Type*} [Fintype I] [DecidableEq I] [CommRing K]
    (a : I → Kˣ) (x : I → K) :
    (diagonalUnitMatrix a)⁻¹.val *ᵥ x = fun i => ((a i)⁻¹ : Kˣ).val * x i := by
  funext i
  exact Matrix.mulVec_diagonal _ _ i

def activeCoordinateUnits {Place K : Type*} [DecidableEq Place] [Monoid K]
    (μ : Place) (a : Kˣ) : Place × Fin 3 → Kˣ :=
  fun i => if i.1 = μ then a else 1

theorem activeCoordinateUnits_prod {Place K : Type*} [Fintype Place] [DecidableEq Place]
    [CommMonoid K] (μ : Place) (a : Kˣ) :
    ∏ i : Place × Fin 3, activeCoordinateUnits μ a i = a ^ 3 := by
  rw [Fintype.prod_prod_type]
  have hinner (v : Place) : (∏ i : Fin 3, activeCoordinateUnits μ a (v, i)) =
      if v = μ then a ^ 3 else 1 := by
    by_cases hv : v = μ <;> simp [activeCoordinateUnits, hv]
  simp_rw [hinner]
  simp

theorem reindexed_activeCoordinateUnits_prod {Place J K : Type*} [Fintype Place] [DecidableEq Place]
    [Fintype J] [CommMonoid K] (e : (Place × Fin 3) ≃ J) (μ : Place) (a : Kˣ) :
    ∏ j : J, activeCoordinateUnits μ a (e.symm j) = a ^ 3 := by
  rw [e.symm.prod_comp, activeCoordinateUnits_prod]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.DiagonalUnits.Realization
