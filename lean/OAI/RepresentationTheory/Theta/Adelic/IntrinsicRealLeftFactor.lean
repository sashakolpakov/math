import OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealWeightedSplitting
import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorModelCongruences
import OAI.RepresentationTheory.Weil.UnitarySplitting.Assembly

/-! # Intrinsic Real Left Factor -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealLeftFactor.Intrinsic

noncomputable section

/-! The first tensor factor in the native oscillator cover, retaining
its exact generic-cell coefficient and centralizer control. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates

theorem native_real_left_factor
    {E : Type} [NormedField E] [Algebra ℝ E]
    [LocallyCompactSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {n m : ℕ}
    (σ : E ≃ₐ[ℝ] E) (H : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin m) (Fin m) E)
    (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)
    (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap ℝ E)) (hQuadratic : Module.finrank ℝ E = 2)
    (hne : ∃ z : E, σ z ≠ z) (hH : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ H = H) (hHdet : H.det ≠ 0)
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun x : ℝ => ψ x)) (hu : ∀ x : ℝ, ‖ψ x‖ = 1)
    (hn : ∃ x : ℝ, ψ x ≠ 1)
    (ω : ℝˣ →ₜ* Circle) (hω : Weil.UnitarySplitting.Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ t : ℝˣ, ∃ Z : ℂ, Z ≠ 0 ∧
      Weil.UnitarySplitting.QuadraticGaussianRegularization.Construction.HasGaussianRegularization μE ψ (fun x => t.val * Algebra.norm ℝ x) Z ∧
      Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Z = (ω t : ℂ) * Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Γ)
    (z : E) (hz : z ≠ 0) (hσz : σ z = -z)
    (u : (Matrix (Fin m) (Fin m) E)ˣ) (a : Fin m → ℝˣ)
    (hdiag : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ u.val * K * u.val = z • Weil.UnitarySplitting.TensorUnitary.Construction.multiplicityForm a)
    (χ : Eˣ →ₜ* Circle) (hχ : Weil.UnitarySplitting.Characters.Construction.HasSplittingRestriction ω m χ) :
    let δ := fun g : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ H => CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.DualPair.Construction.dualPairAction σ H K (g, 1))
    ∃ s : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ H →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ (n * m) ψ,
      (∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ (n * m) ψ (s g) = δ g) ∧
      (∀ g ∈ Weil.UnitarySplitting.Generic.Construction.unitaryGenericDomain σ H, ((δ g).val - 1).det ≠ 0 ∧
        ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ (n * m),
          (∫ x, ((Weil.AdelicSplitting.Oscillator.Construction.localOperator ℝ (n * m) ψ (s g)) f).val x * conj (h.val x)
            ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure ℝ (n * m)) =
            (((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a n * Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ (z • H) χ
              (Weil.UnitarySplitting.FormScaling.Construction.unitaryScaleForm σ H z g))⁻¹ : Circle) : ℂ) *
              Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue ℝ (n * m) ψ (δ g) f.val h.val) ∧
      ∀ b : Weil.AdelicSplitting.Oscillator.Construction.LocalCover ℝ (n * m) ψ,
        (∀ g, Commute (δ g) (Weil.AdelicSplitting.Oscillator.Construction.localProjection ℝ (n * m) ψ b)) → ∀ g, Commute (s g) b := by
  dsimp only
  let Q := z • H
  have hQ : Q.det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hz) hHdet
  have hskew : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ Q = -Q := Weil.UnitarySplitting.FormScaling.Construction.antifixed_hermitian_scale σ z hσz H hH
  let e₀ := Weil.UnitarySplitting.TensorFrameCoordinates.Construction.continuousFrameCoordinates σ H K c Weil.UnitarySplitting.RealFourierUnitary.Construction.real_nondiscrete hEmbedding
  let u₀ := Weil.UnitarySplitting.DualPair.Construction.tensorUnits (1 : (Matrix (Fin n) (Fin n) E)ˣ) u
  let e := Weil.UnitarySplitting.TensorFrameCoordinates.Construction.tensorModelCoordinates finProdFinEquiv u₀ e₀
  have he : ∀ x y, Weil.UnitarySplitting.Oscillator.Construction.standardSymplecticPairing (n * m) (e x) (e y) =
      Algebra.trace ℝ E (Weil.UnitarySplitting.DualPair.Construction.sesquilinear σ (Weil.UnitarySplitting.TensorUnitary.Construction.weightedTensorForm Q a) x y) / 2 :=
    Weil.UnitarySplitting.TensorFrameCoordinates.Construction.tensorModelCoordinates_preserves σ H K c finProdFinEquiv u₀ e₀ rfl _
      (Weil.UnitarySplitting.TensorModelCongruences.Construction.tensorModel_left_congruence σ H K z u a hdiag)
  let scale : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ H →ₜ* Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ Q :=
    ⟨Weil.UnitarySplitting.FormScaling.Construction.unitaryScaleForm σ H z, Weil.UnitarySplitting.Assembly.Construction.unitaryScaleForm_continuous σ H z⟩
  have hmodel (g : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ H) :
      Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he (scale g)) = Weil.UnitarySplitting.DualPair.Construction.dualPairAction σ H K (g, 1) :=
    Weil.UnitarySplitting.TensorFrameCoordinates.Construction.tensorModelCoordinates_action σ H K c finProdFinEquiv u₀ e₀ rfl _ he
      (Weil.UnitarySplitting.TensorUnitary.Construction.weightedTensorUnitary σ Q a (scale g)) (g, 1) (Weil.UnitarySplitting.TensorModelCongruences.Construction.tensorModel_left_intertwines σ H K z u a g)
  obtain ⟨s, hs, hform, hcentral⟩ := IntrinsicRealWeightedSplitting.Intrinsic.native_real_weighted_splitting
    σ H K c (Weil.UnitarySplitting.TensorFrameCoordinates.Construction.symplecticFrame_continuous σ H K c Weil.UnitarySplitting.RealFourierUnitary.Construction.real_nondiscrete hEmbedding).1
      (Weil.UnitarySplitting.TensorFrameCoordinates.Construction.symplecticFrame_continuous σ H K c Weil.UnitarySplitting.RealFourierUnitary.Construction.real_nondiscrete hEmbedding).2
    hE hEmbedding hQuadratic hne ψ hc hu hn ω hω μE Γ hΓ0 hΓ Q hQ hskew a χ hχ e he
  refine ⟨s.comp scale, ?_, ?_, ?_⟩
  · intro g
    exact (hs (scale g)).trans (congrArg (CircleCoordinates.coordinateSymplectic σ H K c) (hmodel g))
  · intro g hg
    have h := hform (scale g) hg
    simp only [MonoidHom.comp_apply] at h
    change ((CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c
      (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he (scale g)))).val - 1).det ≠ 0 ∧ _ at h
    rw [hmodel] at h
    exact h
  · intro b hb g
    apply hcentral b _ (scale g)
    intro t
    obtain ⟨j, rfl⟩ := Weil.UnitarySplitting.FormScaling.Construction.unitaryScaleForm_surjective σ H z hz t
    change Commute (CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c
      (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he (scale j)))) _
    rw [hmodel]
    exact hb j

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealLeftFactor.Intrinsic
