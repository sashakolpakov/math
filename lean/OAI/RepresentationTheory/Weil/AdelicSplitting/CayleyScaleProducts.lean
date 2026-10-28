import OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyMatrixBaseChange
import OAI.RepresentationTheory.Weil.AdelicSplitting.ThetaTest

/-! # Cayley Scale Products -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyScaleProducts.Construction

noncomputable section

/-! Cayley scales on rational matrices have positive products, by the
actual rational Levi coefficient theorem. -/

open scoped Classical _root_.NumberField _root_.Matrix

theorem openCellScale_inverse_coordinate
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    (N : ℕ) (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0)
    (D : CayleyMatrixBaseChange.Construction.PhaseMatrixUnit k N) (hD : D.val = g.val - 1) :
    (Normalization.Construction.openCellScale k N g)⁻¹ =
      (Real.sqrt (Local.FunctionsMetaplectic.Construction.localModulus k (Local.FunctionsMetaplectic.Construction.determinantUnit k (CayleyMatrixBaseChange.Construction.phaseUnitCoordinates k N D))))⁻¹ := by
  rw [Normalization.Construction.openCellScale, dite_eq_left hg]
  congr 3
  apply Units.ext
  change (g.val - 1).det = (Matrix.reindex finSumFinEquiv finSumFinEquiv D.val).det
  rw [Matrix.det_reindex_self, hD]

variable (F : Type) [Field F] [NumberField F] (N : ℕ)
variable (γ : Local.FunctionsMetaplectic.Construction.Symplectic F N) (D : CayleyMatrixBaseChange.Construction.PhaseMatrixUnit F N) (hD : D.val = γ.val - 1)

include hD

theorem rationalDifferenceUnit_local (v : ArchimedeanAdeles.Construction.Places F) :
    (CayleyMatrixBaseChange.Construction.mapPhaseMatrixUnit N (ArchimedeanAdeles.Construction.rationalScalar F v) D).val = (Vacuum.Construction.rationalSymplecticLocal F N v γ).val - 1 := by
  change (D.val).map (ArchimedeanAdeles.Construction.rationalScalar F v) = γ.val.map (ArchimedeanAdeles.Construction.rationalScalar F v) - 1
  rw [hD]
  exact (ArchimedeanAdeles.Construction.rationalScalar F v).mapMatrix.map_sub γ.val 1 |>.trans (by rw [map_one])

theorem rationalDifference_det_local (v : ArchimedeanAdeles.Construction.Places F) :
    ((Vacuum.Construction.rationalSymplecticLocal F N v γ).val - 1).det ≠ 0 := by
  rw [← rationalDifferenceUnit_local F N γ D hD v]
  exact Matrix.GeneralLinearGroup.det_ne_zero _

theorem rational_openCellScale_inverse (v : ArchimedeanAdeles.Construction.Places F) :
    (Normalization.Construction.openCellScale (ArchimedeanAdeles.Construction.Completion F v) N (Vacuum.Construction.rationalSymplecticLocal F N v γ))⁻¹ =
      ThetaTest.Construction.rationalLeviCoefficient F (N + N) (CayleyMatrixBaseChange.Construction.phaseUnitCoordinates F N D) v := by
  rw [openCellScale_inverse_coordinate N _ (rationalDifference_det_local F N γ D hD v)
    (CayleyMatrixBaseChange.Construction.mapPhaseMatrixUnit N (ArchimedeanAdeles.Construction.rationalScalar F v) D) (rationalDifferenceUnit_local F N γ D hD v)]
  unfold ThetaTest.Construction.rationalLeviCoefficient Rational.Construction.localizeLinear
  rw [CayleyMatrixBaseChange.Construction.phaseUnitCoordinates_map]

theorem rational_openCellScale_positive_product (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) :
    ∃ c : ℝ, 0 < c ∧ HasProd
      (fun v => ((Normalization.Construction.openCellScale (ArchimedeanAdeles.Construction.Completion F v) N (Vacuum.Construction.rationalSymplecticLocal F N v γ))⁻¹ : ℂ)) (c : ℂ) := by
  simp only [← Complex.ofReal_inv]
  simp_rw [rational_openCellScale_inverse F N γ D hD]
  exact ThetaTest.Construction.rationalLeviCoefficient_positive_product F (N + N) ψ (CayleyMatrixBaseChange.Construction.phaseUnitCoordinates F N D)
    (RationalLevi.Construction.rationalLeviFamily F (N + N) ψ (CayleyMatrixBaseChange.Construction.phaseUnitCoordinates F N D))
    (RationalLevi.Construction.rationalLeviFamily_spec F (N + N) ψ (CayleyMatrixBaseChange.Construction.phaseUnitCoordinates F N D))

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CayleyScaleProducts.Construction
