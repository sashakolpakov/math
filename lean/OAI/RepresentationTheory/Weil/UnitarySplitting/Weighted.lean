import OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedCayleyMultiplication
import OAI.RepresentationTheory.Weil.UnitarySplitting.GenericCentralizers
import OAI.RepresentationTheory.Weil.UnitarySplitting.GroupTopology

/-! # Weighted -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Weighted.Construction

noncomputable section

/-! A continuous splitting for every weighted tensor unitary model, using
only the prescribed multiplicity restriction of the splitting character. -/

open _root_.Matrix _root_.MeasureTheory

theorem weighted_unitary_splitting_ultra
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
    [CharZero F] [IsUltrametricDist F] [MeasurableSpace F] [BorelSpace F] {m n p q : ℕ}
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (hci : Continuous c.coordinates.symm)
    (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
    (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
    (hne : ∃ z : E, σ z ≠ z)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (hn : ∃ x : F, ψ x ≠ 1)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (Q : Matrix (Fin p) (Fin p) E) (hQ : Q.det ≠ 0) (hskew : DualPair.Construction.adjointMatrix σ Q = -Q)
    (a : Fin q → Fˣ) (χ : Eˣ →ₜ* Circle) (hχ : Characters.Construction.HasSplittingRestriction ω q χ)
    (e : (Fin (p * q) → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
    (he : ∀ x y, Oscillator.Construction.standardSymplecticPairing (m * n) (e x) (e y) =
      Algebra.trace F E (DualPair.Construction.sesquilinear σ (TensorUnitary.Construction.weightedTensorForm Q a) x y) / 2) :
    ∃ s : DualPair.Construction.unitaryGroup σ Q →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ,
      (∀ g, Oscillator.Construction.circleProjection σ H K c ψ (s g) =
        FrameTransport.Construction.frameSymplectic σ H K c (WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g)) ∧
      ∀ (k : FrameTransport.Construction.StandardSymplectic F (m * n)) (b : Oscillator.Construction.CircleExtension σ H K c ψ),
        Oscillator.Construction.circleProjection σ H K c ψ b = FrameTransport.Construction.frameSymplectic σ H K c k →
        (∀ g, Commute (WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g) k) → ∀ g, Commute (s g) b := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let : SecondCountableTopology E := TestSpaceAnalysis.Construction.localField_secondCountable E hE
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : IsTopologicalGroup (Oscillator.Construction.CircleExtension σ H K c ψ) := GroupTopology.Construction.circleExtension_isTopologicalGroup hF hEmbedding σ H K c ψ
  let μF : Measure F := Measure.addHaar
  let μE : Measure E := Measure.addHaar
  let ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) := Measure.addHaar
  obtain ⟨Γ, hΓ0, hΓ⟩ := GaussianCutoffHaar.Construction.ultra_norm_hasGaussianCutoffs hF hE hEmbedding hQuadratic σ hne ω hω μF μE ψ hc hu hn
  let α := WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he
  let D := Generic.Construction.unitaryGenericDomain σ Q
  let A := WeightedCayleyLifts.Construction.weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he
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
    exact WeightedCayleyMultiplication.Construction.weightedRawCayleyLift_multiplication σ H K c hF hE hQuadratic hne ψ hc hu hn ν ω hω
      μE Γ hΓ0 hΓ Q hQ hskew a χ hχ e he g h hg hh hgh
  have hfc : ContinuousOn f D := GenericCharacterCorrection.Construction.characterCorrectedLift_continuousOn ι (Weak.Construction.circleScalar_continuous σ H K c ψ)
    ℓ κ A D (GenericDeterminantCharacter.Construction.genericDeterminantCharacter_continuousOn σ Q hQ χ)
    (WeightedCayleyLifts.Construction.weightedRawCayleyLift_continuousOn σ H K c hF ψ hc hu hn ν Q a e he hci)
  let s := GenericCharacterCorrection.Construction.genericExtensionContinuousHom D f hthick hmul (Generic.Construction.unitaryGenericDomain_open σ Q) hfc
  refine ⟨s, ?_, ?_⟩
  · apply GenericCharacterCorrection.Construction.genericExtensionHom_projection D f hthick hmul (Oscillator.Construction.circleProjection σ H K c ψ).toMonoidHom
      ((FrameTransport.Construction.frameSymplectic σ H K c).comp α)
    intro g hg
    change Oscillator.Construction.circleProjection σ H K c ψ (ι ((ℓ * κ g)⁻¹) * A g) = FrameTransport.Construction.frameSymplectic σ H K c (α g)
    rw [map_mul, Oscillator.Construction.circleScalar_projects_to_one, one_mul]
    exact WeightedCayleyLifts.Construction.weightedRawCayleyLift_projection σ H K c hF ψ hc hu hn ν Q a e he g hg
  · intro k b hb hk g
    change Commute (GenericCharacterCorrection.Construction.genericExtension D f hthick g) b
    apply GenericCentralizers.Construction.genericExtension_commutes D f hthick hmul b _ g
    intro t ht
    apply GenericCentralizers.Construction.characterCorrectedLift_commutes ι hcentral ℓ κ A t b
    change Commute (WeightedCayleyLifts.Construction.weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he t) b
    rw [WeightedCayleyLifts.Construction.weightedRawCayleyLift_apply σ H K c hF ψ hc hu hn ν Q a e he t ht]
    apply CayleyCentralizers.Construction.ultraCayleyLift_centralizer σ H K c hF ψ hc hu hn ν
      (α t) (WeightedCayleyLifts.Construction.weightedFrameDifference σ Q a e t ht).toLinearEquiv
      (WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he t ht) k _ b hb
    intro x
    exact congrArg (fun j : FrameTransport.Construction.StandardSymplectic F (m * n) => j.val x) (hk t).eq

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Weighted.Construction
