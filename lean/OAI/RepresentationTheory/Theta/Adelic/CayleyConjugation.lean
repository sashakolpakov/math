import OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseMeasure

/-! # Cayley Conjugation -/

namespace OAI.RepresentationTheory.Theta.Adelic.CayleyConjugation

noncomputable section

/-! The corrected Cayley phase and its Haar factor are equivariant under
actual symplectic conjugation. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseMeasure.Construction

variable {k : Type} [NormedField k] (N : ℕ) (b g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N)

theorem conjugate_difference : (b * g * b⁻¹).val - 1 = b.val * (g.val - 1) * (b⁻¹).val := by
  have hb : b.val * (b⁻¹).val = 1 := by
    change (b * b⁻¹).val = 1
    rw [mul_inv_cancel]
    rfl
  change (b.val * g.val * (b⁻¹).val) - 1 = _
  rw [mul_sub, sub_mul, mul_one, hb]

theorem conjugate_difference_det : ((b * g * b⁻¹).val - 1).det = (g.val - 1).det := by
  rw [conjugate_difference, Matrix.det_mul, Matrix.det_mul,
    SymplecticGroup.det_eq_one b.property, SymplecticGroup.det_eq_one (b⁻¹).property,
    one_mul, mul_one]

variable [LocallyCompactSpace k]

theorem openCellScale_conjugate : Weil.AdelicSplitting.Normalization.Construction.openCellScale k N (b * g * b⁻¹) = Weil.AdelicSplitting.Normalization.Construction.openCellScale k N g := by
  classical
  exact congrArg (fun t : k => if ht : t ≠ 0 then Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Units.mk0 t ht)) else 0)
    (conjugate_difference_det N b g)

variable [CharZero k]

omit [LocallyCompactSpace k] [CharZero k] in
theorem difference_conjugate_apply (hg : (g.val - 1).det ≠ 0)
    (hbg : ((b * g * b⁻¹).val - 1).det ≠ 0) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N (b * g * b⁻¹) hbg (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b x) =
      Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N g hg x) := by
  rw [Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply, Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply,
    Weil.Local.FunctionsMetaplectic.Construction.symplecticAction_mul, Weil.Local.FunctionsMetaplectic.Construction.symplecticAction_mul, Weil.Local.FunctionsMetaplectic.Construction.symplecticAction_cancel_inv]
  exact (Matrix.mulVec_sub b.val _ _).symm

omit [LocallyCompactSpace k] [CharZero k] in
theorem difference_conjugate_inverse (hg : (g.val - 1).det ≠ 0)
    (hbg : ((b * g * b⁻¹).val - 1).det ≠ 0) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N (b * g * b⁻¹) hbg).symm (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b v) =
      Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b ((Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N g hg).symm v) := by
  apply (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N (b * g * b⁻¹) hbg).injective
  rw [LinearEquiv.apply_symm_apply, difference_conjugate_apply N b g hg hbg, LinearEquiv.apply_symm_apply]

omit [LocallyCompactSpace k] [CharZero k] in
theorem cayleyPhase_conjugate (hg : (g.val - 1).det ≠ 0)
    (hbg : ((b * g * b⁻¹).val - 1).det ≠ 0) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N (b * g * b⁻¹) hbg (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b v) =
      Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg v := by
  change Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing k N ((Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N (b * g * b⁻¹) hbg).symm
      (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b v)) (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction b v) / 2 = _
  rw [difference_conjugate_inverse N b g hg hbg, Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing_preserved]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.CayleyConjugation
