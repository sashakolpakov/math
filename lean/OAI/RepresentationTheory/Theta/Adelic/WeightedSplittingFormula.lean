import OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedCayleyMultiplication
import OAI.RepresentationTheory.Weil.UnitarySplitting.GenericCentralizers
import OAI.RepresentationTheory.Weil.UnitarySplitting.GroupTopology

/-! # Weighted Splitting Formula -/

namespace OAI.RepresentationTheory.Theta.Adelic.WeightedSplittingFormula

noncomputable section

/-! A constructed weighted splitting together with its exact formula on
the generic cell, retaining the actual norm Gaussian and Cayley operator. -/

open _root_.Matrix _root_.MeasureTheory

theorem weighted_unitary_splitting_formula
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
    [CharZero F] [IsUltrametricDist F] [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology F] {m n p q : ℕ}
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Weil.UnitarySplitting.Oscillator.Construction.SymplecticFrame σ H K) (hci : Continuous c.coordinates.symm)
    (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
    (hne : ∃ z : E, σ z ≠ z)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (hn : ∃ x : F, ψ x ≠ 1)
    (ω : Fˣ →ₜ* Circle) (hω : Weil.UnitarySplitting.Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ν : Measure (Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))) [ν.IsAddHaarMeasure]
    (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ t : Fˣ, Weil.UnitarySplitting.GaussianCutoff.Construction.HasGaussianCutoffs μE ψ (fun x => (t : F) * Algebra.norm F x)
      (Weil.UnitarySplitting.GaussianCutoffHaar.Construction.normGaussianValue ω Γ t))
    (Q : Matrix (Fin p) (Fin p) E) (hQ : Q.det ≠ 0) (hskew : Weil.UnitarySplitting.DualPair.Construction.adjointMatrix σ Q = -Q)
    (a : Fin q → Fˣ) (χ : Eˣ →ₜ* Circle) (hχ : Weil.UnitarySplitting.Characters.Construction.HasSplittingRestriction ω q χ)
    (e : (Fin (p * q) → E) ≃L[F] Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
    (he : ∀ x y, Weil.UnitarySplitting.Oscillator.Construction.standardSymplecticPairing (m * n) (e x) (e y) =
      Algebra.trace F E (Weil.UnitarySplitting.DualPair.Construction.sesquilinear σ (Weil.UnitarySplitting.TensorUnitary.Construction.weightedTensorForm Q a) x y) / 2) :
    ∃ s : Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ Q →ₜ* Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ,
      (∀ g, Weil.UnitarySplitting.Oscillator.Construction.circleProjection σ H K c ψ (s g) =
        Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g)) ∧
      (∀ g ∈ Weil.UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q,
        s g = Weil.UnitarySplitting.Oscillator.Construction.circleScalar σ H K c ψ ((Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p *
          Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g)⁻¹) *
          Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he g) ∧
      ∀ (k : Weil.UnitarySplitting.FrameTransport.Construction.StandardSymplectic F (m * n)) (b : Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ),
        Weil.UnitarySplitting.Oscillator.Construction.circleProjection σ H K c ψ b = Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c k →
        (∀ g, Commute (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g) k) → ∀ g, Commute (s g) b := by
  let : SecondCountableTopology E := Weil.UnitarySplitting.TestSpaceAnalysis.Construction.localField_secondCountable E hE
  let : IsTopologicalGroup (Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ) := Weil.UnitarySplitting.GroupTopology.Construction.circleExtension_isTopologicalGroup hF hEmbedding σ H K c ψ
  let α := Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he
  let D := Weil.UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q
  let A := Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he
  let ℓ := Weil.UnitarySplitting.WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p
  let κ := Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ
  let ι := Weil.UnitarySplitting.Oscillator.Construction.circleScalar σ H K c ψ
  let f := Weil.UnitarySplitting.GenericCharacterCorrection.Construction.characterCorrectedLift ι ℓ κ A
  have hcentral : ∀ z : Circle, ∀ b : Weil.UnitarySplitting.Oscillator.Construction.CircleExtension σ H K c ψ, Commute (ι z) b :=
    Weil.UnitarySplitting.Oscillator.Construction.circleScalar_central σ H K c ψ
  have hthick : ∀ t : Finset (Weil.UnitarySplitting.DualPair.Construction.unitaryGroup σ Q), ∃ u, ∀ g ∈ t, g * u ∈ D :=
    Weil.UnitarySplitting.Generic.Construction.unitaryGenericDomain_thick σ Q (Weil.UnitarySplitting.TracePairing.Construction.quadratic_automorphism_involutive hQuadratic σ) hne
  have hmul : ∀ g ∈ D, ∀ h ∈ D, g * h ∈ D → f (g * h) = f g * f h := by
    intro g hg h hh hgh
    apply Eq.symm
    apply Weil.UnitarySplitting.GenericCharacterCorrection.Construction.characterCorrectedLift_mul ι hcentral ℓ κ A g h
    exact Weil.UnitarySplitting.WeightedCayleyMultiplication.Construction.weightedRawCayleyLift_multiplication σ H K c hF hE hQuadratic hne ψ hc hu hn ν ω hω
      μE Γ hΓ0 hΓ Q hQ hskew a χ hχ e he g h hg hh hgh
  have hfc : ContinuousOn f D := Weil.UnitarySplitting.GenericCharacterCorrection.Construction.characterCorrectedLift_continuousOn ι (Weil.UnitarySplitting.Weak.Construction.circleScalar_continuous σ H K c ψ)
    ℓ κ A D (Weil.UnitarySplitting.GenericDeterminantCharacter.Construction.genericDeterminantCharacter_continuousOn σ Q hQ χ)
    (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedRawCayleyLift_continuousOn σ H K c hF ψ hc hu hn ν Q a e he hci)
  let s := Weil.UnitarySplitting.GenericCharacterCorrection.Construction.genericExtensionContinuousHom D f hthick hmul (Weil.UnitarySplitting.Generic.Construction.unitaryGenericDomain_open σ Q) hfc
  refine ⟨s, ?_, ?_, ?_⟩
  · apply Weil.UnitarySplitting.GenericCharacterCorrection.Construction.genericExtensionHom_projection D f hthick hmul (Weil.UnitarySplitting.Oscillator.Construction.circleProjection σ H K c ψ).toMonoidHom
      ((Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c).comp α)
    intro g hg
    change Weil.UnitarySplitting.Oscillator.Construction.circleProjection σ H K c ψ (ι ((ℓ * κ g)⁻¹) * A g) = Weil.UnitarySplitting.FrameTransport.Construction.frameSymplectic σ H K c (α g)
    rw [map_mul, Weil.UnitarySplitting.Oscillator.Construction.circleScalar_projects_to_one, one_mul]
    exact Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedRawCayleyLift_projection σ H K c hF ψ hc hu hn ν Q a e he g hg
  · intro g hg
    exact Weil.UnitarySplitting.GenericCharacterCorrection.Construction.genericExtension_eq D f hthick hmul g hg
  · intro k b hb hk g
    change Commute (Weil.UnitarySplitting.GenericCharacterCorrection.Construction.genericExtension D f hthick g) b
    apply Weil.UnitarySplitting.GenericCentralizers.Construction.genericExtension_commutes D f hthick hmul b _ g
    intro t ht
    apply Weil.UnitarySplitting.GenericCentralizers.Construction.characterCorrectedLift_commutes ι hcentral ℓ κ A t b
    change Commute (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he t) b
    rw [Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedRawCayleyLift_apply σ H K c hF ψ hc hu hn ν Q a e he t ht]
    apply Weil.UnitarySplitting.CayleyCentralizers.Construction.ultraCayleyLift_centralizer σ H K c hF ψ hc hu hn ν
      (α t) (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameDifference σ Q a e t ht).toLinearEquiv
      (Weil.UnitarySplitting.WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he t ht) k _ b hb
    intro x
    exact congrArg (fun j : Weil.UnitarySplitting.FrameTransport.Construction.StandardSymplectic F (m * n) => j.val x) (hk t).eq

end

end OAI.RepresentationTheory.Theta.Adelic.WeightedSplittingFormula
