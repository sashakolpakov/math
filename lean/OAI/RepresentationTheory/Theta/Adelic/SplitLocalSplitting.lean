import OAI.RepresentationTheory.Theta.Adelic.SplitStableNormalization
import OAI.RepresentationTheory.Theta.Adelic.NormalizationConjugation

/-! # Split Local Splitting -/

namespace OAI.RepresentationTheory.Theta.Adelic.SplitLocalSplitting

noncomputable section

/-! The exact normalized split unitary splitting in the supplied tensor
frame, over every characteristic-zero local field. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitFrame OAI.RepresentationTheory.Theta.Adelic.GeneralSplitLift OAI.RepresentationTheory.Theta.Adelic.FrameChange
open OAI.RepresentationTheory.Theta.Adelic.SplitStableNormalization OAI.RepresentationTheory.Theta.Adelic.NormalizationConjugation

variable {k : Type} [NormedField k] [CharZero k] [CompleteSpace k] [LocallyCompactSpace k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {d : k}

theorem split_local_splitting (hd : d ≠ 0) (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)
    (n m : ℕ) (hnm : 0 < n * m)
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (hH : H.val.conjTranspose = H.val) (hK : K.val.conjTranspose = -K.val)
    (P : Weil.AdelicSplitting.TensorSpace.Construction.SymplecticFrame d n m H.val K.val)
    (χV χW : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle)
    (hχV : ∀ a : kˣ, χV (Units.map (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom a) = 1)
    (hχW : ∀ a : kˣ, χW (Units.map (algebraMap k (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)).toMonoidHom a) = 1)
    (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hc : Continuous ψ)
    (hu : ∀ x : k, ‖ψ x‖ = 1) (hn : ∃ x : k, ψ x ≠ 1) :
    ∃ s : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
      (∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (s g) = Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P g) ∧
      (∀ (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ),
        u.val = g.val.val - 1 → ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m),
        (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (s (g, 1)) f).val x * conj (h.val x)
          ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
          (χW ((Weil.AdelicSplitting.Normalization.Construction.deltaUnit d hd) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ) *
            Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (g, 1)) f.val h.val) ∧
      (∀ (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ),
        u.val = g.val.val - 1 → ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m),
        (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (s (1, g)) f).val x * conj (h.val x)
          ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
          (χV (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ) *
            Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (1, g)) f.val h.val) := by
  obtain ⟨s, hp, w, hw, hs⟩ := GeneralSplitLift.exists_split_lift r hr hr0 n m H K χV χW hnd ψ hnm hH hK P hc hu hn
  refine ⟨s, hp, ?_, ?_⟩
  · intro g u hgu f h
    apply NormalizationConjugation.weak_normalization_pullback (n * m) ψ hnd hc hu hn w (s (g, 1))
      (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (g, 1)) _ _ f h
    intro f' h'
    rw [hs, hw, FrameChange.frameChange_conjugates]
    exact SplitStableNormalization.first_stable_normalization r hr hr0 n m H K χV χW hnd ψ hc hu hn hd hH hK hχW g u hgu f' h'
  · intro g u hgu f h
    apply NormalizationConjugation.weak_normalization_pullback (n * m) ψ hnd hc hu hn w (s (1, g))
      (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P (1, g)) _ _ f h
    intro f' h'
    rw [hs, hw, FrameChange.frameChange_conjugates]
    exact SplitStableNormalization.second_stable_normalization r hr hr0 n m H K χV χW hnd ψ hc hu hn hH hK hχV g u hgu f' h'

end

end OAI.RepresentationTheory.Theta.Adelic.SplitLocalSplitting
