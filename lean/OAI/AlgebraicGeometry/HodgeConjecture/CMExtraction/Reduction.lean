import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralCoordinates
import OAI.RepresentationTheory.Hecke.RadialDilation.DiagonalUnits
import OAI.RepresentationTheory.Theta.Geometric.SphericalGU

/-! # Reduction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Reduction.Iwasawa

noncomputable section

/-! Correct the integral GL3 reduction by its determinant unit, obtaining
an actual SL3(Zq) Iwasawa factor without changing triangularity. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.DiagonalUnits.Realization
open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]

theorem integralSL3_reduction (g : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3 q) :
    ∃ U : Matrix.SpecialLinearGroup (Fin 3) ℤ_[q],
      (g * Matrix.SpecialLinearGroup.map (PadicInt.Coe.ringHom (p := q)) U).val.IsUpperTriangular := by
  obtain ⟨U, hU⟩ := PadicIntegralCoordinates.Iwasawa.integralGL_reduction q (Matrix.SpecialLinearGroup.toGL g)
  let δ := Matrix.GeneralLinearGroup.det U
  let C := RepresentationTheory.Hecke.RadialDilation.DiagonalUnits.Realization.diagonalUnitMatrix (![δ⁻¹, 1, 1] : Fin 3 → ℤ_[q]ˣ)
  have hCdet : Matrix.GeneralLinearGroup.det C = δ⁻¹ := by
    rw [RepresentationTheory.Hecke.RadialDilation.DiagonalUnits.Realization.diagonalUnitMatrix_det]
    simp [Fin.prod_univ_three]
  have hV : (U * C).val.det = 1 := by
    change ((Matrix.GeneralLinearGroup.det (U * C) : ℤ_[q]ˣ) : ℤ_[q]) = 1
    rw [map_mul, hCdet]
    change ((δ * δ⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) = 1
    rw [mul_inv_cancel, Units.val_one]
  have hCtri : (PadicIntegralCoordinates.Iwasawa.integralGLMap q C).val.IsUpperTriangular := by
    intro i j hij
    change ((C.val i j : ℤ_[q]) : ℚ_[q]) = 0
    have hne : i ≠ j := ne_of_gt hij
    simp [C, RepresentationTheory.Hecke.RadialDilation.DiagonalUnits.Realization.diagonalUnitMatrix, hne]
  refine ⟨⟨(U * C).val, hV⟩, ?_⟩
  change ((Matrix.SpecialLinearGroup.toGL g) * PadicIntegralCoordinates.Iwasawa.integralGLMap q (U * C)).val.IsUpperTriangular
  rw [map_mul, ← mul_assoc]
  exact hU.mul hCtri

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Reduction.Iwasawa
