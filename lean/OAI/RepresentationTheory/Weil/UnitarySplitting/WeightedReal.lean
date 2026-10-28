import OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedRealMultiplication
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyCentralizers
import OAI.RepresentationTheory.Weil.UnitarySplitting.GenericCentralizers
import OAI.RepresentationTheory.Weil.UnitarySplitting.GroupTopology

/-! # Weighted Real -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedReal.Construction

noncomputable section

/-! A continuous splitting for every weighted tensor unitary model, using
only the prescribed multiplicity restriction of the splitting character. -/

open _root_.Matrix _root_.MeasureTheory

theorem weighted_unitary_splitting_real
    {E : Type} [NormedField E] [Algebra ℝ E]
    [LocallyCompactSpace E] [FiniteDimensional ℝ E] {m n p q : ℕ}
    (σ : E ≃ₐ[ℝ] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (hci : Continuous c.coordinates.symm)
    (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap ℝ E)) (hQuadratic : Module.finrank ℝ E = 2)
    (hne : ∃ z : E, σ z ≠ z)
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun x : ℝ => ψ x)) (hu : ∀ x : ℝ, ‖ψ x‖ = 1)
    (hn : ∃ x : ℝ, ψ x ≠ 1)
    (ω : ℝˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (Q : Matrix (Fin p) (Fin p) E) (hQ : Q.det ≠ 0) (hskew : DualPair.Construction.adjointMatrix σ Q = -Q)
    (a : Fin q → ℝˣ) (χ : Eˣ →ₜ* Circle) (hχ : Characters.Construction.HasSplittingRestriction ω q χ)
    (e : (Fin (p * q) → E) ≃L[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))
    (he : ∀ x y, Oscillator.Construction.standardSymplecticPairing (m * n) (e x) (e y) =
      Algebra.trace ℝ E (DualPair.Construction.sesquilinear σ (TensorUnitary.Construction.weightedTensorForm Q a) x y) / 2) :
    ∃ s : DualPair.Construction.unitaryGroup σ Q →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ,
      (∀ g, Oscillator.Construction.circleProjection σ H K c ψ (s g) =
        FrameTransport.Construction.frameSymplectic σ H K c (WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g)) ∧
      ∀ (k : FrameTransport.Construction.StandardSymplectic ℝ (m * n)) (b : Oscillator.Construction.CircleExtension σ H K c ψ),
        Oscillator.Construction.circleProjection σ H K c ψ b = FrameTransport.Construction.frameSymplectic σ H K c k →
        (∀ g, Commute (WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g) k) → ∀ g, Commute (s g) b := by
  let : SecondCountableTopology E := TestSpaceAnalysis.Construction.localField_secondCountable E hE
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : IsTopologicalGroup (Oscillator.Construction.CircleExtension σ H K c ψ) := GroupTopology.Construction.circleExtension_isTopologicalGroup RealFourierUnitary.Construction.real_nondiscrete hEmbedding σ H K c ψ
  let μE : Measure E := Measure.addHaar
  let ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n)) := Measure.addHaar
  obtain ⟨Γ, hΓ0, hΓ⟩ := ArchNormRegularization.Construction.arch_norm_hasGaussianRegularization (RingEquiv.refl ℝ) continuous_id hEmbedding hQuadratic ω hω μE ψ hc hu hn
  let α := WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he
  let D := Generic.Construction.unitaryGenericDomain σ Q
  let A := WeightedRealCayleyLifts.Construction.weightedRealRawCayleyLift σ H K c ψ hc hu hn ν Q a e he
  let ℓ := WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p
  let κ := GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ
  let ι := Oscillator.Construction.circleScalar σ H K c ψ
  let f := GenericCharacterCorrection.Construction.characterCorrectedLift ι ℓ κ A
  have hcentral : ∀ z : Circle, ∀ b : Oscillator.Construction.CircleExtension σ H K c ψ, Commute (ι z) b :=
    Oscillator.Construction.circleScalar_central σ H K c ψ
  have hthick : ∀ t : Finset (DualPair.Construction.unitaryGroup σ Q), ∃ u, ∀ g ∈ t, g * u ∈ D :=
    Generic.Construction.unitaryGenericDomain_thick σ Q (TracePairing.Construction.quadratic_automorphism_involutive hQuadratic σ) hne
  have hmul : ∀ g ∈ D, ∀ h ∈ D, g * h ∈ D → f (g * h) = f g * f h := by
    intro g hg h hh hgh
    apply Eq.symm
    apply GenericCharacterCorrection.Construction.characterCorrectedLift_mul ι hcentral ℓ κ A g h
    exact WeightedRealMultiplication.Construction.weightedRealRawCayleyLift_multiplication σ H K c hE hQuadratic hne ψ hc hu hn ν ω hω
      μE Γ hΓ0 hΓ Q hQ hskew a χ hχ e he g h hg hh hgh
  have hfc : ContinuousOn f D := GenericCharacterCorrection.Construction.characterCorrectedLift_continuousOn ι (Weak.Construction.circleScalar_continuous σ H K c ψ)
    ℓ κ A D (GenericDeterminantCharacter.Construction.genericDeterminantCharacter_continuousOn σ Q hQ χ)
    (WeightedRealCayleyLifts.Construction.weightedRealRawCayleyLift_continuousOn σ H K c ψ hc hu hn ν Q a e he hci)
  let s := GenericCharacterCorrection.Construction.genericExtensionContinuousHom D f hthick hmul (Generic.Construction.unitaryGenericDomain_open σ Q) hfc
  refine ⟨s, ?_, ?_⟩
  · apply GenericCharacterCorrection.Construction.genericExtensionHom_projection D f hthick hmul (Oscillator.Construction.circleProjection σ H K c ψ).toMonoidHom
      ((FrameTransport.Construction.frameSymplectic σ H K c).comp α)
    intro g hg
    change Oscillator.Construction.circleProjection σ H K c ψ (ι ((ℓ * κ g)⁻¹) * A g) = FrameTransport.Construction.frameSymplectic σ H K c (α g)
    rw [map_mul, Oscillator.Construction.circleScalar_projects_to_one, one_mul]
    exact WeightedRealCayleyLifts.Construction.weightedRealRawCayleyLift_projection σ H K c ψ hc hu hn ν Q a e he g hg
  · intro k b hb hk g
    change Commute (GenericCharacterCorrection.Construction.genericExtension D f hthick g) b
    apply GenericCentralizers.Construction.genericExtension_commutes D f hthick hmul b _ g
    intro t ht
    apply GenericCentralizers.Construction.characterCorrectedLift_commutes ι hcentral ℓ κ A t b
    change Commute (WeightedRealCayleyLifts.Construction.weightedRealRawCayleyLift σ H K c ψ hc hu hn ν Q a e he t) b
    rw [WeightedRealCayleyLifts.Construction.weightedRealRawCayleyLift_apply σ H K c ψ hc hu hn ν Q a e he t ht]
    apply RealCayleyCentralizers.Construction.realCayleyLift_centralizer σ H K c ψ hc hu hn ν
      (α t) (WeightedCayleyLifts.Construction.weightedFrameDifference σ Q a e t ht).toLinearEquiv
      (WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he t ht) k _ b hb
    intro x
    exact congrArg (fun j : FrameTransport.Construction.StandardSymplectic ℝ (m * n) => j.val x) (hk t).eq

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedReal.Construction
