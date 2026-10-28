import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.AdelicSplitting.DeterminantMeasure

/-! # Phase Measure -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseMeasure.Construction

noncomputable section

/-! Haar measure in phase coordinates, including the exact determinant
Jacobian of the open-cell difference and invariance under symplectic maps. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.DeterminantMeasure.LocalAnalysis _root_.MeasureTheory
open scoped _root_.Matrix

variable (k : Type) [NormedField k] (N : ℕ)

def phaseCoordinates : Local.FunctionsMetaplectic.Construction.PhaseSpace k N ≃L[k] Local.FunctionsMetaplectic.Construction.Position k (N + N) :=
  ContinuousLinearEquiv.piCongrLeft k (fun _ : Fin (N + N) => k) finSumFinEquiv

variable [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]

omit [LocallyCompactSpace k] [BorelSpace k] [SecondCountableTopology k] in
theorem phaseCoordinates_measurePreserving (μ : Measure k) [SigmaFinite μ] :
    MeasurePreserving (phaseCoordinates k N)
      (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) (Measure.pi (fun _ : Fin (N + N) => μ)) :=
  measurePreserving_piCongrLeft (fun _ : Fin (N + N) => μ) finSumFinEquiv

theorem symplecticAction_measurePreserving (μ : Measure k) [μ.IsAddHaarMeasure]
    (g : Local.FunctionsMetaplectic.Construction.Symplectic k N) : MeasurePreserving (Local.FunctionsMetaplectic.Construction.symplecticAction g)
      (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) (Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) := by
  have hd : g.val.det = 1 := SymplecticGroup.det_eq_one g.property
  have hm := DeterminantMeasure.LocalAnalysis.map_matrix_haar_eq_smul μ (show g.val.det ≠ 0 by rw [hd]; exact one_ne_zero)
  rw [hd, inv_one, map_one, ENNReal.coe_one, one_smul] at hm
  exact ⟨(LinearMap.continuous_on_pi (Matrix.toLin' g.val)).measurable, hm⟩

theorem phaseMatrix_inverse_integral {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : Measure k) [μ.IsAddHaarMeasure] (M : Matrix ι ι k) (hM : M.det ≠ 0)
    (f : (ι → k) → ℝ) :
    (∫ x, f (M⁻¹ *ᵥ x) ∂Measure.pi (fun _ : ι => μ)) =
      (DeterminantMeasure.LocalAnalysis.haarModulus k M.det : ℝ) * ∫ x, f x ∂Measure.pi (fun _ : ι => μ) := by
  let e := Matrix.toLinearEquiv (Pi.basisFun k ι) M⁻¹
    (isUnit_iff_ne_zero.mpr (by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hM))
  have hc : Continuous e := LinearMap.continuous_on_pi e.toLinearMap
  have hi : Continuous e.symm := LinearMap.continuous_on_pi e.symm.toLinearMap
  let em : (ι → k) ≃ᵐ (ι → k) :=
    { __ := e.toEquiv
      measurable_toFun := hc.measurable
      measurable_invFun := hi.measurable }
  have he (x : ι → k) : M⁻¹ *ᵥ x = em x := by
    simp [em, e, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
  simp_rw [he]
  rw [← integral_map_equiv em f]
  have hm := DeterminantMeasure.LocalAnalysis.map_matrix_haar_eq_smul μ
    (show (M⁻¹).det ≠ 0 by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hM)
  have hem : (em : (ι → k) → (ι → k)) = Matrix.toLin' M⁻¹ := funext fun x => (he x).symm
  rw [hem, hm, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', inv_inv, integral_smul_measure,
    ENNReal.coe_toReal]
  rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseMeasure.Construction
