import OAI.RepresentationTheory.Theta.Adelic.FieldCoverPairing
import OAI.RepresentationTheory.Theta.Adelic.FieldWeakNormalization

/-! # Field Cover Normalization -/

namespace OAI.RepresentationTheory.Theta.Adelic.FieldCoverNormalization

noncomputable section

/-! A proved weak normalization equation in field coordinates gives the
same native equation after continuous oscillator pullback. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.FieldCoverPullback OAI.RepresentationTheory.Theta.Adelic.FieldCoverPairing OAI.RepresentationTheory.Theta.Adelic.FieldWeakNormalization

variable {k l : Type} [NormedField k] [NormedField l] [LocallyCompactSpace k] [LocallyCompactSpace l]
variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
variable [SecondCountableTopology k] [SecondCountableTopology l]

theorem normalized_cover_pullback
    (e : k ≃+* l) (he : Continuous e) (hi : Continuous e.symm) (N : ℕ) (ψ : AddChar k ℂ)
    [(Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure l (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ)).IsAddHaarMeasure]
    (hmap : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).map e = Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure l (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ))
    (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ)) (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (c : ℂ)
    (hform : ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat l N,
      (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) a f).val x * conj (h.val x)
        ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure l N) =
        c * Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue l N (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ) (Weil.Local.FieldFourier.Construction.fieldSymplecticMap e N g) f.val h.val)
    (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (FieldCoverPullback.fieldCoverPullback e he hi N ψ a) f).val x * conj (h.val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) =
      c * Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k N ψ g f.val h.val := by
  rw [FieldCoverPairing.fieldCoverPullback_pairing, hform, mul_left_comm]
  exact congrArg (fun z : ℂ => c * z) (FieldWeakNormalization.correctedWeakOpenCellValue_field e he hi N ψ hmap g f.val h.val)

end

end OAI.RepresentationTheory.Theta.Adelic.FieldCoverNormalization
