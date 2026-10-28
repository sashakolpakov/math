import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak

/-! # Vacuum Pairing -/

namespace OAI.RepresentationTheory.Theta.Adelic.VacuumPairing

noncomputable section

/-! A unitary oscillator fixes a test vector when its diagonal matrix
coefficient equals that vector's energy. This converts the unramified
weak-integral calculation into exact vacuum preservation. -/

open _root_.MeasureTheory
open scoped ComplexConjugate InnerProductSpace

open OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (N : ℕ) (ψ : AddChar k ℂ)

theorem oscillator_fixes_of_pairing (a : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N)
    (hpair : (∫ x, (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f).val x * conj (f.val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k N) = (Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N f : ℂ)) :
    Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f = f := by
  let T := Weil.UnitarySplitting.Weak.Construction.testToL2 k N
  have hE (u : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : ‖T u‖ ^ 2 = Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N u := by
    have hn : 0 ≤ Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N u := integral_nonneg (fun x => sq_nonneg ‖u.val x‖)
    rw [Weil.UnitarySplitting.Weak.Construction.testToL2_norm, Real.sq_sqrt hn]
  have hp : (⟪T f, T (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f)⟫_ℂ).re = Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N f := by
    rw [Weil.UnitarySplitting.Weak.Construction.testToL2_inner, hpair]
    rfl
  have hs := norm_sub_sq (𝕜 := ℂ) (T (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f)) (T f)
  rw [inner_re_symm] at hs
  change ‖T (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f) - T f‖ ^ 2 =
    ‖T (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f)‖ ^ 2 -
      2 * (⟪T f, T (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f)⟫_ℂ).re + ‖T f‖ ^ 2 at hs
  have ha : Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f) = Weil.Local.FunctionsMetaplectic.Construction.l2Energy k N f := a.property.1 f
  rw [hp, hE, hE, ha] at hs
  have hz : ‖T (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f) - T f‖ = 0 := by nlinarith [norm_nonneg (T (Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ a f) - T f)]
  apply Weil.UnitarySplitting.Weak.Construction.testToL2_injective k N
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end

end OAI.RepresentationTheory.Theta.Adelic.VacuumPairing
