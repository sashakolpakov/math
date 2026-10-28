import OAI.RepresentationTheory.Theta.Adelic.WeightedRealSplittingFormula
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealCayleyPairing
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicWeightedSplitting
import OAI.RepresentationTheory.Theta.Adelic.CircleCoordinateCentralizer

/-! # Intrinsic Real Weighted Splitting -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealWeightedSplitting.Intrinsic

noncomputable section

/-! A continuous weighted unitary splitting in the native matrix
oscillator cover, with its exact corrected weak-integral formula. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates OAI.RepresentationTheory.Theta.Adelic.IntrinsicCayleyPairing.Intrinsic

theorem native_real_weighted_splitting
    {E : Type} [NormedField E] [Algebra ℝ E]
    [LocallyCompactSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {n m p q : ℕ}
    (σ : E ≃ₐ[ℝ] E) (H : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin m) (Fin m) E)
    (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)
    (hcc : Continuous c.coordinates) (hci : Continuous c.coordinates.symm)
    (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap ℝ E)) (hQuadratic : Module.finrank ℝ E = 2)
    (hne : ∃ z : E, σ z ≠ z)
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun x : ℝ => ψ x)) (hu : ∀ x : ℝ, ‖ψ x‖ = 1)
    (hn : ∃ x : ℝ, ψ x ≠ 1)
    (ω : ℝˣ →ₜ* Circle) (hω : Weil.UnitarySplitting.Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ t : ℝˣ, ∃ Z : ℂ, Z ≠ 0 ∧
      Weil.UnitarySplitting.QuadraticGaussianRegularization.Construction.HasGaussianRegularization μE ψ (fun x => t.val * Algebra.norm ℝ x) Z ∧
      Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Z = (ω t : ℂ) * Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Γ)
    (Q : Matrix (Fin p) (Fin p) E) (hQ : Q.det ≠ 0) (hskew : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ Q = -Q)
    (a : Fin q → ℝˣ) (χ : Eˣ →ₜ* Circle) (hχ : Weil.UnitarySplitting.Characters.Construction.HasSplittingRestriction ω q χ)
    (e : (Fin (p * q) → E) ≃L[ℝ] Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (n * m))
    (he : ∀ x y, Weil.UnitarySplitting.Oscillator.Construction.standardSymplecticPairing (n * m) (e x) (e y) =
      Algebra.trace ℝ E (Weil.UnitarySplitting.DualPair.Construction.sesquilinear σ (Weil.UnitarySplitting.TensorUnitary.Construction.weightedTensorForm Q a) x y) / 2) :
    let δ := (CircleCoordinates.coordinateSymplectic σ H K c).comp
      ((Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c).comp (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he))
    ∃ s : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ Q →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ (n * m) ψ,
      (∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ (n * m) ψ (s g) = δ g) ∧
      (∀ g ∈ Weil.UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q, ((δ g).val - 1).det ≠ 0 ∧
        ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (n * m),
          (∫ x, ((Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ (n * m) ψ (s g)) f).val x * conj (h.val x)
            ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ (n * m)) =
            (((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p * Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g)⁻¹ : Circle) : ℂ) *
              Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue ℝ (n * m) ψ (δ g) f.val h.val) ∧
      ∀ b : Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ (n * m) ψ,
        (∀ g, Commute (δ g) (Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ (n * m) ψ b)) → ∀ g, Commute (s g) b := by
  dsimp only
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure :=
    Weil.AdelicSplitting.FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ ψ
      (Weil.AdelicSplitting.RealNormalization.LocalAnalysis.real_fourier_analysis (n * m) ψ hc hu hn).1
  let ν := Measure.pi (fun _ : Fin (n * m) ⊕ Fin (n * m) => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ)
  let : ν.IsAddHaarMeasure := by dsimp [ν]; infer_instance
  obtain ⟨s, hs, hsform, hscomm⟩ := WeightedRealSplittingFormula.weighted_real_splitting_formula
    σ H K c hci hE hEmbedding hQuadratic hne ψ hc hu hn ω hω μE ν Γ hΓ0 hΓ Q hQ hskew a χ hχ e he
  let δ := (CircleCoordinates.coordinateSymplectic σ H K c).comp
    ((Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c).comp (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he))
  let t := (CircleCoordinates.coordinateCoverContinuous σ H K c ψ hcc).comp s
  refine ⟨t, ?_, ?_, ?_⟩
  · intro g
    change CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.Oscillator.Construction.circleProjection σ H K c ψ (s g)) = δ g
    rw [hs]
    rfl
  · intro g hg
    let α := Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g
    let D := (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameDifference σ Q a e g hg).toLinearEquiv
    have hα (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (n * m)) : α.val x = Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (δ g) x :=
      IntrinsicCayleyPairing.Intrinsic.frameAction_eq_native σ H K c α (δ g) rfl x
    have hD (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (n * m)) : D x = α.val x - x :=
      Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he g hg x
    have hδ : ((δ g).val - 1).det ≠ 0 :=
      IntrinsicWeightedSplitting.Intrinsic.openCell_of_difference (n * m) (δ g) D (fun x => (hD x).trans (congrArg (fun z => z - x) (hα x)))
    refine ⟨hδ, ?_⟩
    intro f h
    have hpair := IntrinsicRealCayleyPairing.Intrinsic.realCayley_pairing_native σ H K c ψ hc hu hn α D hD (δ g) hδ hα f h
    have hform := hsform g hg
    rw [Weil.UnitarySplitting.WeightedRealCayleyLifts.Construction.weightedRealRawCayleyLift_apply σ H K c ψ hc hu hn ν Q a e he g hg] at hform
    have hop : Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ (n * m) ψ (t g) f =
        (((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p * Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g)⁻¹ : Circle) : ℂ) •
          (Weil.UnitarySplitting.RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν α D hD).val.2 f := by
      change (s g).val.2 f = _
      rw [hform]
      rfl
    rw [hop]
    change (∫ x, ((((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p * Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g)⁻¹ : Circle) : ℂ) *
      ((Weil.UnitarySplitting.RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν α D hD).val.2 f).val x) * conj (h.val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ (n * m)) = _
    simp only [mul_assoc]
    rw [integral_const_mul, hpair]
  · intro b hb g
    exact CircleCoordinateCentralizer.native_centralizer σ H K c ψ
      (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he) s.toMonoidHom hscomm b hb g

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealWeightedSplitting.Intrinsic
