import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitLift
import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitOpenCell
import OAI.RepresentationTheory.Theta.Adelic.LeviWeakNormalization

/-! # Split Stable Normalization -/

namespace OAI.RepresentationTheory.Theta.Adelic.SplitStableNormalization

noncomputable section

/-! Exact normalization of both factors in the stable split tensor frame. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitFrame OAI.RepresentationTheory.Theta.Adelic.GeneralSplitTensorAction OAI.RepresentationTheory.Theta.Adelic.GeneralSplitCharacter
open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitContinuous OAI.RepresentationTheory.Theta.Adelic.GeneralSplitLift OAI.RepresentationTheory.Theta.Adelic.GeneralSplitOpenCell
open OAI.RepresentationTheory.Theta.Adelic.LeviWeakNormalization

variable {k : Type} [NormedField k] [CharZero k] [CompleteSpace k] [LocallyCompactSpace k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {d : k}
variable (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
variable (χV χW : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle)
variable (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
variable (hc : Continuous ψ) (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1)

include hc hu hn in
theorem stableLift_weak (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) (U : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k (n * m))
    (hU : U.val = (GeneralSplitTensorAction.linearPair r hr hr0 n m H K g).val - 1) (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m)) :
    (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (GeneralSplitLift.stableLift r hr hr0 n m H K χV χW hnd ψ g) f).val x *
      conj (h.val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
    (GeneralSplitLift.pairCharacter r hr hr0 n m H K χV χW g : ℂ) *
      Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ (Weil.Local.Generators.Construction.leviSymplectic (GeneralSplitTensorAction.linearPair r hr hr0 n m H K g)) f.val h.val := by
  have he (x : Weil.Local.FunctionsMetaplectic.Construction.Position k (n * m)) :
      (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (GeneralSplitLift.stableLift r hr hr0 n m H K χV χW hnd ψ g) f).val x =
        (GeneralSplitLift.pairCharacter r hr hr0 n m H K χV χW g : ℂ) *
          (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (Weil.AdelicSplitting.NormalizationLevi.Construction.localLeviHom (n * m) ψ (GeneralSplitTensorAction.linearPair r hr hr0 n m H K g)) f).val x := by
    rw [GeneralSplitLift.stableLift_operator]
    change _ = (GeneralSplitLift.pairCharacter r hr hr0 n m H K χV χW g : ℂ) *
      ((Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ (GeneralSplitTensorAction.linearPair r hr hr0 n m H K g)).val.2 f).val x
    rw [Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply, mul_assoc]
  simp_rw [he, mul_assoc]
  rw [integral_const_mul, LeviWeakNormalization.positiveLevi_corrected_weak (n * m) hnd ψ hc hu hn _ U hU]

omit [CompleteSpace k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] in
theorem pairCharacter_first (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) :
    GeneralSplitLift.pairCharacter r hr hr0 n m H K χV χW (g, 1) = GeneralSplitCharacter.unitaryCharacter r hr hr0 H χW.toMonoidHom g := by
  change GeneralSplitContinuous.continuousUnitaryCharacter r hr hr0 H χW g * GeneralSplitContinuous.continuousUnitaryCharacter r hr hr0 K χV 1 = _
  rw [map_one, mul_one]
  rfl

omit [CompleteSpace k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] in
theorem pairCharacter_second (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) :
    GeneralSplitLift.pairCharacter r hr hr0 n m H K χV χW (1, g) = GeneralSplitCharacter.unitaryCharacter r hr hr0 K χV.toMonoidHom g := by
  change GeneralSplitContinuous.continuousUnitaryCharacter r hr hr0 H χW 1 * GeneralSplitContinuous.continuousUnitaryCharacter r hr hr0 K χV g = _
  rw [map_one, one_mul]
  rfl

include hc hu hn in
theorem first_stable_normalization (hd : d ≠ 0)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (hχW : ∀ a : kˣ, χW (Units.map (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom a) = 1)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hgu : u.val = g.val.val - 1)
    (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m)) :
    (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (GeneralSplitLift.stableLift r hr hr0 n m H K χV χW hnd ψ (g, 1)) f).val x *
      conj (h.val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
    (χW ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ) *
      Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ
        (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val (GeneralSplitFrame.splitFrame r hr hr0 n m H K hH hK) (g, 1)) f.val h.val := by
  rw [stableLift_weak r hr hr0 n m H K χV χW hnd ψ hc hu hn (g, 1)
    (GeneralSplitOpenCell.firstDifference r hr hr0 n m u) (GeneralSplitOpenCell.firstDifference_val r hr hr0 n m H K g u hgu),
    pairCharacter_first, GeneralSplitTensorAction.splitFrame_action]
  congr 2
  symm
  change χW.toMonoidHom ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H *
    Matrix.GeneralLinearGroup.det u) = _
  have he := GeneralSplitCharacter.first_argument_character r hr hr0 hd H hH χW.toMonoidHom hχW g u hgu
  rw [Fintype.card_fin] at he
  exact he

include hc hu hn in
theorem second_stable_normalization
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (hχV : ∀ a : kˣ, χV (Units.map (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom a) = 1)
    (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) (hgu : u.val = g.val.val - 1)
    (f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m)) :
    (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (GeneralSplitLift.stableLift r hr hr0 n m H K χV χW hnd ψ (1, g)) f).val x *
      conj (h.val x) ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
    (χV (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ) *
      Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ
        (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val (GeneralSplitFrame.splitFrame r hr hr0 n m H K hH hK) (1, g)) f.val h.val := by
  rw [stableLift_weak r hr hr0 n m H K χV χW hnd ψ hc hu hn (1, g)
    (GeneralSplitOpenCell.secondDifference r hr hr0 n m u) (GeneralSplitOpenCell.secondDifference_val r hr hr0 n m H K g u hgu),
    pairCharacter_second, GeneralSplitTensorAction.splitFrame_action]
  congr 2
  exact (GeneralSplitCharacter.second_argument_character r hr hr0 K hK χV.toMonoidHom hχV g u hgu).symm

end

end OAI.RepresentationTheory.Theta.Adelic.SplitStableNormalization
