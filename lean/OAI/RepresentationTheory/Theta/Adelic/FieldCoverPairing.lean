import OAI.RepresentationTheory.Theta.Adelic.FieldCoverPullback
import OAI.RepresentationTheory.Theta.Adelic.FieldMeasures

/-! # Field Cover Pairing -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldCoverPairing

noncomputable section

/-! Exact weak operator pairings for the continuous field pullback,
with the same reference Haar factor as the corrected weak integral. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.FieldCoverPullback OAI.RepresentationTheory.Theta.Adelic.FieldMeasures

variable {k l : Type} [NormedField k] [NormedField l] [LocallyCompactSpace k] [LocallyCompactSpace l]
variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
variable [SecondCountableTopology k] [SecondCountableTopology l]

theorem fieldCoverPullback_pairing
    (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (N : ℕ) (ψ : AddChar k ℂ)
    (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ)) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (FieldCoverPullback.fieldCoverPullback e he hi N ψ a) f).val x * conj (h.val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
      (FieldMeasures.fieldPositionHaarScale e he hi N : ℂ) *
        ∫ y, (Weil.AdelicSplitting.Oscillator.Construction.localOperator l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a (Weil.Local.FieldCoordinates.Construction.testSpaceTransport (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N) f)).val y *
          conj ((Weil.Local.FieldCoordinates.Construction.testSpaceTransport (Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N) h).val y)
            ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure l N := by
  let p := Weil.Local.FieldCoordinates.Construction.fieldPositionEquiv e he hi N
  let C := Weil.Local.FieldCoordinates.Construction.testSpaceTransport p
  rw [FieldCoverPullback.fieldCoverPullback_operator]
  have hr := FieldMeasures.fieldPositionHaar_integral e he hi N
    (fun x => (C.symm (Weil.AdelicSplitting.Oscillator.Construction.localOperator l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a (C f))).val x * conj (h.val x))
  refine hr.trans ?_
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change (Weil.AdelicSplitting.Oscillator.Construction.localOperator l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a (C f)).val (p (p.symm y)) * conj (h.val (p.symm y)) =
      (Weil.AdelicSplitting.Oscillator.Construction.localOperator l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a (C f)).val y * conj (h.val (p.symm y))
    rw [p.apply_symm_apply]

end

end OAI.RepresentationTheory.Theta.Adelic.FieldCoverPairing
