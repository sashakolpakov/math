import OAI.RepresentationTheory.Theta.Adelic.WeightedSplittingFormula
import OAI.RepresentationTheory.Theta.Adelic.IntrinsicCayleyPairing
import OAI.RepresentationTheory.Theta.Adelic.CircleCoordinateCentralizer

/-! # Intrinsic Weighted Splitting -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicWeightedSplitting.Intrinsic

noncomputable section

/-! A continuous weighted unitary splitting in the native matrix
oscillator cover, with its exact corrected weak-integral formula. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

open OAI.RepresentationTheory.Theta.Adelic.CircleCoordinates OAI.RepresentationTheory.Theta.Adelic.IntrinsicCayleyPairing.Intrinsic

theorem openCell_of_difference
    {k : Type} [NormedField k] (N : ℕ) (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N)
    (D : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N ≃ₗ[k] Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N)
    (hD : ∀ x, D x = Weil.Local.FunctionsMetaplectic.Construction.symplecticAction g x - x) : (g.val - 1).det ≠ 0 := by
  have hs : Function.Surjective (g.val - 1).mulVec := by
    intro y
    refine ⟨D.symm y, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact (hD (D.symm y)).symm.trans (D.apply_symm_apply y)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp hs))

theorem native_weighted_splitting
    {k E : Type} [NormedField k] [NormedField E] [Algebra k E]
    [CompleteSpace k] [LocallyCompactSpace k] [LocallyCompactSpace E] [FiniteDimensional k E]
    [CharZero k] [IsUltrametricDist k] [MeasurableSpace k] [BorelSpace k]
    [MeasurableSpace E] [BorelSpace E] {n m p q : ℕ}
    (σ : E ≃ₐ[k] E) (H : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin m) (Fin m) E)
    (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K)
    (hcc : Continuous c.coordinates) (hci : Continuous c.coordinates.symm)
    (hk : ¬ DiscreteTopology k) (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap k E)) (hQuadratic : Module.finrank k E = 2)
    (hne : ∃ z : E, σ z ≠ z)
    (ψ : AddChar k ℂ) (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
    (hn : ∃ x : k, ψ x ≠ 1)
    (ω : kˣ →ₜ* Circle) (hω : Weil.UnitarySplitting.Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ t : kˣ, Weil.UnitarySplitting.GaussianCutoff.Construction.HasGaussianCutoffs μE ψ (fun x => t.val * Algebra.norm k x) (Weil.UnitarySplitting.GaussianCutoffHaar.Construction.normGaussianValue ω Γ t))
    (Q : Matrix (Fin p) (Fin p) E) (hQ : Q.det ≠ 0) (hskew : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ Q = -Q)
    (a : Fin q → kˣ) (χ : Eˣ →ₜ* Circle) (hχ : Weil.UnitarySplitting.Characters.Construction.HasSplittingRestriction ω q χ)
    (e : (Fin (p * q) → E) ≃L[k] Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m))
    (he : ∀ x y, Weil.UnitarySplitting.Oscillator.Construction.standardSymplecticPairing (n * m) (e x) (e y) =
      Algebra.trace k E (Weil.UnitarySplitting.DualPair.Construction.sesquilinear σ (Weil.UnitarySplitting.TensorUnitary.Construction.weightedTensorForm Q a) x y) / 2) :
    let δ := (CircleCoordinates.coordinateSymplectic σ H K c).comp
      ((Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c).comp (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he))
    ∃ s : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ Q →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
      (∀ g, Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ (s g) = δ g) ∧
      (∀ g ∈ Weil.UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q, ((δ g).val - 1).det ≠ 0 ∧
        ∀ f h : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k (n * m),
          (∫ x, ((Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (s g)) f).val x * conj (h.val x)
            ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) =
            (((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p * Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g)⁻¹ : Circle) : ℂ) *
              Weil.AdelicSplitting.CorrectedNormalization.Construction.correctedWeakOpenCellValue k (n * m) ψ (δ g) f.val h.val) ∧
      ∀ b : Weil.AdelicSplitting.Oscillator.Construction.LocalCover k (n * m) ψ,
        (∀ g, Commute (δ g) (Weil.AdelicSplitting.Oscillator.Construction.localProjection k (n * m) ψ b)) → ∀ g, Commute (s g) b := by
  dsimp only
  let : SecondCountableTopology k := Weil.UnitarySplitting.TestSpaceAnalysis.Construction.localField_secondCountable k hk
  let : ProperSpace k := Weil.AdelicSplitting.TestSpace.LocalAnalysis.localField_proper k hk
  let : (Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    Weil.AdelicSplitting.FourierTools.LocalAnalysis.selfDualMeasure_isAddHaarMeasure_of_scale_pos k ψ
      (Weil.AdelicSplitting.NonarchimedeanReference.LocalAnalysis.nonarchimedean_one_coordinate_normalization ψ hu hc hn).1
  let ν := Measure.pi (fun _ : Fin (n * m) ⊕ Fin (n * m) => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ)
  let : ν.IsAddHaarMeasure := by dsimp [ν]; infer_instance
  obtain ⟨s, hs, hsform, hscomm⟩ := WeightedSplittingFormula.weighted_unitary_splitting_formula
    σ H K c hci hk hE hEmbedding hQuadratic hne ψ hc hu hn ω hω μE ν Γ hΓ0 hΓ Q hQ hskew a χ hχ e he
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
    have hα (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m)) : α.val x = Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (δ g) x :=
      IntrinsicCayleyPairing.Intrinsic.frameAction_eq_native σ H K c α (δ g) rfl x
    have hD (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k (n * m)) : D x = α.val x - x :=
      Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he g hg x
    have hδ : ((δ g).val - 1).det ≠ 0 :=
      openCell_of_difference (n * m) (δ g) D (fun x => (hD x).trans (congrArg (fun z => z - x) (hα x)))
    refine ⟨hδ, ?_⟩
    intro f h
    have hpair := IntrinsicCayleyPairing.Intrinsic.ultraCayley_pairing_native σ H K c hk ψ hc hu hn α D hD (δ g) hδ hα f h
    have hform := hsform g hg
    rw [Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedRawCayleyLift_apply σ H K c hk ψ hc hu hn ν Q a e he g hg] at hform
    have hop : Weil.AdelicSplitting.Oscillator.Construction.localOperator k (n * m) ψ (t g) f =
        (((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p * Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g)⁻¹ : Circle) : ℂ) •
          (Weil.UnitarySplitting.CanonicalCayleyLift.Construction.ultraCayleyLift σ H K c hk ψ hc hu hn ν α D hD).val.2 f := by
      change (s g).val.2 f = _
      rw [hform]
      rfl
    rw [hop]
    change (∫ x, ((((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p * Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g)⁻¹ : Circle) : ℂ) *
      ((Weil.UnitarySplitting.CanonicalCayleyLift.Construction.ultraCayleyLift σ H K c hk ψ hc hu hn ν α D hD).val.2 f).val x) * conj (h.val x)
      ∂ Weil.UnitarySplitting.Weak.Construction.referencePositionMeasure k (n * m)) = _
    simp only [mul_assoc]
    rw [integral_const_mul, hpair]
  · intro b hb g
    exact CircleCoordinateCentralizer.native_centralizer σ H K c ψ
      (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he) s.toMonoidHom hscomm b hb g

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicWeightedSplitting.Intrinsic
