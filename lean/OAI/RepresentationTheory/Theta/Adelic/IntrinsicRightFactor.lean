import OAI.RepresentationTheory.Theta.Adelic.IntrinsicWeightedSplitting
import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorModelCongruences

/-! # Intrinsic Right Factor -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicRightFactor.Intrinsic

noncomputable section

/-! The second tensor factor in the native oscillator cover, retaining
the actual weighted Gaussian and generic determinant coefficient. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Weil.UnitarySplitting.TensorModelCongruences.Construction
open OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates

theorem native_right_factor
    {k E : Type} [NormedField k] [NormedField E] [Algebra k E]
    [CompleteSpace k] [LocallyCompactSpace k] [LocallyCompactSpace E] [FiniteDimensional k E]
    [CharZero k] [IsUltrametricDist k] [MeasurableSpace k] [BorelSpace k]
    [MeasurableSpace E] [BorelSpace E] {n m : ℕ}
    (σ : E ≃ₐ[k] E) (H : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin m) (Fin m) E)
    (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)
    (hk : ¬ DiscreteTopology k) (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap k E)) (hQuadratic : Module.finrank k E = 2)
    (hne : ∃ z : E, σ z ≠ z) (hK : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ K = -K) (hKdet : K.det ≠ 0)
    (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
    (hn : ∃ x : k, ψ x ≠ 1)
    (ω : kˣ →ₜ* Circle) (hω : Weil.UnitarySplitting.Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ t : kˣ, Weil.UnitarySplitting.GaussianCutoff.Construction.HasGaussianCutoffs μE ψ (fun x => t.val * Algebra.norm k x) (Weil.UnitarySplitting.GaussianCutoffHaar.Construction.normGaussianValue ω Γ t))
    (u : (Matrix (Fin n) (Fin n) E)ˣ) (a : Fin n → kˣ)
    (hdiag : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ u.val * H * u.val = Weil.UnitarySplitting.TensorUnitary.Construction.multiplicityForm a)
    (χ : Eˣ →ₜ* Circle) (hχ : Weil.UnitarySplitting.Characters.Construction.HasSplittingRestriction ω n χ) :
    let δ := fun g : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ K => CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.DualPair.Construction.dualPairAction σ H K (1, g))
    ∃ s : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ K →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
      (∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (s g) = δ g) ∧
      (∀ g ∈ Weil.UnitarySplitting.Generic.Construction.unitaryGenericDomain σ K, ((δ g).val - 1).det ≠ 0 ∧
        ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m),
          (∫ x, ((Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (s g)) f).val x * conj (h.val x)
            ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
            (((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a m * Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ K χ g)⁻¹ : Circle) : ℂ) *
              Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ (δ g) f.val h.val) ∧
      ∀ b : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
        (∀ g, Commute (δ g) (Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ b)) → ∀ g, Commute (s g) b := by
  dsimp only
  let e₀ := Weil.UnitarySplitting.TensorFrameCoordinates.Construction.continuousFrameCoordinates σ H K c hk hEmbedding
  let u₀ := Weil.UnitarySplitting.DualPair.Construction.tensorUnits u (1 : (Matrix (Fin m) (Fin m) E)ˣ)
  let e := Weil.UnitarySplitting.TensorFrameCoordinates.Construction.tensorModelCoordinates Weil.UnitarySplitting.TensorModelCongruences.Construction.swappedTensorIndex u₀ e₀
  have he : ∀ x y, Weil.UnitarySplitting.Oscillator.Construction.standardSymplecticPairing (n * m) (e x) (e y) =
      Algebra.trace k E (Weil.UnitarySplitting.DualPair.Construction.sesquilinear σ (Weil.UnitarySplitting.TensorUnitary.Construction.weightedTensorForm K a) x y) / 2 :=
    Weil.UnitarySplitting.TensorFrameCoordinates.Construction.tensorModelCoordinates_preserves σ H K c Weil.UnitarySplitting.TensorModelCongruences.Construction.swappedTensorIndex u₀ e₀ rfl _
      (Weil.UnitarySplitting.TensorModelCongruences.Construction.tensorModel_right_congruence σ H K u a hdiag)
  have hmodel (g : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ K) :
      Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ K a e he g) = Weil.UnitarySplitting.DualPair.Construction.dualPairAction σ H K (1, g) :=
    Weil.UnitarySplitting.TensorFrameCoordinates.Construction.tensorModelCoordinates_action σ H K c Weil.UnitarySplitting.TensorModelCongruences.Construction.swappedTensorIndex u₀ e₀ rfl _ he
      (Weil.UnitarySplitting.TensorUnitary.Construction.weightedTensorUnitary σ K a g) (1, g) (Weil.UnitarySplitting.TensorModelCongruences.Construction.tensorModel_right_intertwines σ H K u a g)
  obtain ⟨s, hs, hform, hcentral⟩ := IntrinsicWeightedSplitting.Intrinsic.native_weighted_splitting
    σ H K c (Weil.UnitarySplitting.TensorFrameCoordinates.Construction.symplecticFrame_continuous σ H K c hk hEmbedding).1
      (Weil.UnitarySplitting.TensorFrameCoordinates.Construction.symplecticFrame_continuous σ H K c hk hEmbedding).2
    hk hE hEmbedding hQuadratic hne ψ hc hu hn ω hω μE Γ hΓ0 hΓ K hKdet hK a χ hχ e he
  refine ⟨s, ?_, ?_, ?_⟩
  · intro g
    exact (hs g).trans (congrArg (CircleCoordinates.coordinateSymplectic σ H K c) (hmodel g))
  · intro g hg
    have h := hform g hg
    simp only [MonoidHom.comp_apply] at h
    change ((CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c
      (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ K a e he g))).val - 1).det ≠ 0 ∧ _ at h
    rw [hmodel] at h
    exact h
  · intro b hb g
    apply hcentral b _ g
    intro j
    change Commute (CircleCoordinates.coordinateSymplectic σ H K c (Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c
      (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ K a e he j))) _
    rw [hmodel]
    exact hb j

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicRightFactor.Intrinsic
