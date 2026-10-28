import OAI.RepresentationTheory.Theta.Adelic.IntrinsicCayleyPairing
import OAI.RepresentationTheory.Theta.Adelic.RealCayleyNormalization

/-! # Intrinsic Real Cayley Pairing -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealCayleyPairing.Intrinsic

noncomputable section

/-! The actual real canonical Cayley operator agrees with the corrected
native weak integral for every compatible matrix coordinate action. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

theorem realCayley_pairing_native
    {E : Type} [NormedField E] [Algebra ℝ E] {n m : ℕ}
    (σ : E ≃ₐ[ℝ] E) (H : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin m) (Fin m) E)
    (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun x : ℝ => ψ x))
    (hu : ∀ x : ℝ, ‖ψ x‖ = 1) (hn : ∃ x : ℝ, ψ x ≠ 1)
    (α : Weil.UnitarySplitting.FrameTransport.Construction.StandardSymplectic ℝ (n * m))
    (D : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (n * m) ≃ₗ[ℝ] Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (n * m)) (hD : ∀ x, D x = α.val x - x)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℝ (n * m)) (hg : (g.val - 1).det ≠ 0)
    (hα : ∀ x, α.val x = Weil.Local.FunctionsMetaplectic.Construction.symplecticAction g x) :
    let ν := Measure.pi (fun _ : Fin (n * m) ⊕ Fin (n * m) => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)
    letI : ν.IsAddHaarMeasure := by
      let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure :=
        Weil.AdelicSplitting.FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ (Weil.AdelicSplitting.RealNormalization.LocalAnalysis.real_fourier_analysis (n * m) ψ hc hu hn).1
      infer_instance
    ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (n * m),
      (∫ x, ((Weil.UnitarySplitting.RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν α D hD).val.2 f).val x * conj (h.val x)
        ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ (n * m)) =
        Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue ℝ (n * m) ψ g f.val h.val := by
  have heα : α = Weil.AdelicSplitting.CorrectedNormalization.Construction.standardSymplecticOfMatrix ℝ (n * m) g := by
    apply Subtype.ext
    exact LinearEquiv.ext hα
  subst α
  have heD : D = Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference ℝ (n * m) g hg := by
    apply LinearEquiv.ext
    intro x
    exact (hD x).trans (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply ℝ (n * m) g hg x).symm
  subst D
  dsimp only
  exact (RealCayleyNormalization.real_cayley_radius_and_pairing σ H K c ψ hc hu hn g hg).2

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealCayleyPairing.Intrinsic
