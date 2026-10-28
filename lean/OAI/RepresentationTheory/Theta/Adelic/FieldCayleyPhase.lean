import OAI.RepresentationTheory.Weil.Local.FieldFourier
import OAI.RepresentationTheory.Weil.Local.FieldCoordinates
import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.UnitarySplitting.FieldCoordinates

/-! # Field Cayley Phase -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldCayleyPhase

noncomputable section

/-! The corrected native Cayley quadratic phase and positive modulus
normalization commute with changes of topological field coordinates. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction
open OAI.RepresentationTheory.Weil.UnitarySplitting.FieldCoordinates.Construction (coordinateFieldEquiv)

variable {k l : Type} [NormedField k] [NormedField l]
variable (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (N : ℕ)

theorem field_openCell_det (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) :
    ((Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g).val - 1).det = e (g.val - 1).det := by
  change ((e.toRingHom.mapMatrix g.val) - 1).det = _
  rw [← e.toRingHom.mapMatrix.map_one, ← map_sub, ← RingHom.map_det]
  rfl

theorem field_openCell (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) :
    ((Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g).val - 1).det ≠ 0 := by
  rw [field_openCell_det]
  exact (map_ne_zero e).mpr hg

theorem schrodingerPairing_field (x y : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing l N (fun i => e (x i)) (fun i => e (y i)) = e (Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing k N x y) := by
  rw [Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing_eq_standard, Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing_eq_standard]
  simp only [Weil.UnitarySplitting.Oscillator.Construction.standardSymplecticPairing, map_sum, map_sub, map_mul]

theorem openCellDifference_field (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference l N (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g) (field_openCell e N g hg)
      (fun i => e (x i)) = fun i => e (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N g hg x i) := by
  rw [Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply, Weil.Local.FieldFourier.Construction.fieldSymplecticMap_action, Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply]
  funext i
  exact (e.map_sub _ _).symm

theorem openCellDifference_symm_field (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference l N (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g) (field_openCell e N g hg)).symm
      (fun i => e (x i)) = fun i => e ((Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N g hg).symm x i) := by
  apply (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference l N (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g) (field_openCell e N g hg)).injective
  rw [LinearEquiv.apply_symm_apply, openCellDifference_field e N g hg, LinearEquiv.apply_symm_apply]

theorem schrodingerCayleyPhase_field (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase l N (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g) (field_openCell e N g hg)
      (fun i => e (x i)) = e (Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N g hg x) := by
  unfold Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase Weil.UnitarySplitting.CayleyCompositionPhase.Construction.cayleyWeylPhase
  rw [openCellDifference_symm_field, schrodingerPairing_field, map_div₀, map_ofNat]

variable [LocallyCompactSpace k] [LocallyCompactSpace l]
variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]

include he hi in
theorem openCellScale_field (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (hg : (g.val - 1).det ≠ 0) :
    Weil.AdelicSplitting.Normalization.Construction.openCellScale l N (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g) = Weil.AdelicSplitting.Normalization.Construction.openCellScale k N g := by
  rw [Weil.AdelicSplitting.Normalization.Construction.openCellScale, dite_eq_left (field_openCell e N g hg), Weil.AdelicSplitting.Normalization.Construction.openCellScale, dite_eq_left hg]
  have hunit : Units.mk0 ((Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g).val - 1).det (field_openCell e N g hg) =
      Units.map e.toMonoidHom (Units.mk0 (g.val - 1).det hg) := Units.ext (field_openCell_det e N g)
  rw [hunit, ← Weil.Local.FieldCoordinates.Construction.field_localModulus e he hi]

end

end OAI.RepresentationTheory.Theta.Adelic.FieldCayleyPhase
