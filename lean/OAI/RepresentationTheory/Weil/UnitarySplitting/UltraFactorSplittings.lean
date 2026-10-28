import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorModelCongruences
import OAI.RepresentationTheory.Weil.UnitarySplitting.Assembly

/-! # Ultra Factor Splittings -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.UltraFactorSplittings.Construction

noncomputable section

/-! The two actual tensor factors over nonarchimedean local fields. -/

open _root_.Matrix

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
variable [CharZero F] [IsUltrametricDist F] [MeasurableSpace F] [BorelSpace F] {m n : ℕ}
variable (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K)
variable (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
variable (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
variable (hne : ∃ z : E, σ z ≠ z)
variable (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
variable (hn : ∃ x : F, ψ x ≠ 1)
variable (characters : Characters.Construction.SplittingCharacters F E m n)

include hF hE hEmbedding hQuadratic hne hc hu hn characters

theorem ultra_left_factor_splitting
    (hH : DualPair.Construction.adjointMatrix σ H = H) (hK : DualPair.Construction.adjointMatrix σ K = -K)
    (hHdet : H.det ≠ 0) (hKdet : K.det ≠ 0) :
    ∃ s : DualPair.Construction.unitaryGroup σ H →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ,
      (∀ g, Oscillator.Construction.circleProjection σ H K c ψ (s g) = DualPair.Construction.dualPairAction σ H K (g, 1)) ∧
      ∀ b : Oscillator.Construction.CircleExtension σ H K c ψ,
        (∀ g, Commute (DualPair.Construction.dualPairAction σ H K (g, 1)) (Oscillator.Construction.circleProjection σ H K c ψ b)) →
        ∀ g, Commute (s g) b := by
  obtain ⟨z, hz0, hz⟩ := NormOneParameters.Construction.exists_nonzero_antifixed σ (TracePairing.Construction.quadratic_automorphism_involutive hQuadratic σ) hne
  obtain ⟨u, a, ha⟩ := FormScaling.Construction.skewHermitian_diagonal_units σ hQuadratic hne K hK hKdet z hz0 hz
  let Q := z • H
  have hQ : Q.det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hz0) hHdet
  have hskew : DualPair.Construction.adjointMatrix σ Q = -Q := FormScaling.Construction.antifixed_hermitian_scale σ z hz H hH
  let e₀ := TensorFrameCoordinates.Construction.continuousFrameCoordinates σ H K c hF hEmbedding
  let u₀ := DualPair.Construction.tensorUnits (1 : (Matrix (Fin m) (Fin m) E)ˣ) u
  let e := TensorFrameCoordinates.Construction.tensorModelCoordinates finProdFinEquiv u₀ e₀
  have he : ∀ x y, Oscillator.Construction.standardSymplecticPairing (m * n) (e x) (e y) =
      Algebra.trace F E (DualPair.Construction.sesquilinear σ (TensorUnitary.Construction.weightedTensorForm Q a) x y) / 2 :=
    TensorFrameCoordinates.Construction.tensorModelCoordinates_preserves σ H K c finProdFinEquiv u₀ e₀ rfl _
      (TensorModelCongruences.Construction.tensorModel_left_congruence σ H K z u a ha)
  let α := WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he
  let scale : DualPair.Construction.unitaryGroup σ H →ₜ* DualPair.Construction.unitaryGroup σ Q :=
    ⟨FormScaling.Construction.unitaryScaleForm σ H z, Assembly.Construction.unitaryScaleForm_continuous σ H z⟩
  have hmodel (g : DualPair.Construction.unitaryGroup σ H) :
      FrameTransport.Construction.frameSymplectic σ H K c (α (scale g)) = DualPair.Construction.dualPairAction σ H K (g, 1) :=
    TensorFrameCoordinates.Construction.tensorModelCoordinates_action σ H K c finProdFinEquiv u₀ e₀ rfl _ he
      (TensorUnitary.Construction.weightedTensorUnitary σ Q a (scale g)) (g, 1)
      (TensorModelCongruences.Construction.tensorModel_left_intertwines σ H K z u a g)
  obtain ⟨s, hs, hscomm⟩ := Weighted.Construction.weighted_unitary_splitting_ultra σ H K c
    (TensorFrameCoordinates.Construction.symplecticFrame_continuous σ H K c hF hEmbedding).2 hF hE hEmbedding hQuadratic hne
    ψ hc hu hn characters.quadratic characters.quadratic_kernel Q hQ hskew a
    characters.skewHermitian characters.skewHermitian_restriction e he
  refine ⟨s.comp scale, ?_, ?_⟩
  · intro g
    exact (hs (scale g)).trans (hmodel g)
  · intro b hb g
    apply Assembly.Construction.frameSplitting_centralizer σ H K c ψ α s.toMonoidHom hscomm b _ (scale g)
    intro t
    obtain ⟨k, rfl⟩ := FormScaling.Construction.unitaryScaleForm_surjective σ H z hz0 t
    change Commute (FrameTransport.Construction.frameSymplectic σ H K c (α (scale k))) _
    rw [hmodel]
    exact hb k

theorem ultra_right_factor_splitting
    (hH : DualPair.Construction.adjointMatrix σ H = H) (hK : DualPair.Construction.adjointMatrix σ K = -K)
    (hHdet : H.det ≠ 0) (hKdet : K.det ≠ 0) :
    ∃ s : DualPair.Construction.unitaryGroup σ K →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ,
      ∀ g, Oscillator.Construction.circleProjection σ H K c ψ (s g) = DualPair.Construction.dualPairAction σ H K (1, g) := by
  obtain ⟨u, a, ha⟩ := FormScaling.Construction.hermitian_diagonal_units σ hQuadratic hne H hH hHdet
  let e₀ := TensorFrameCoordinates.Construction.continuousFrameCoordinates σ H K c hF hEmbedding
  let u₀ := DualPair.Construction.tensorUnits u (1 : (Matrix (Fin n) (Fin n) E)ˣ)
  let e := TensorFrameCoordinates.Construction.tensorModelCoordinates TensorModelCongruences.Construction.swappedTensorIndex u₀ e₀
  have he : ∀ x y, Oscillator.Construction.standardSymplecticPairing (m * n) (e x) (e y) =
      Algebra.trace F E (DualPair.Construction.sesquilinear σ (TensorUnitary.Construction.weightedTensorForm K a) x y) / 2 :=
    TensorFrameCoordinates.Construction.tensorModelCoordinates_preserves σ H K c TensorModelCongruences.Construction.swappedTensorIndex u₀ e₀ rfl _
      (TensorModelCongruences.Construction.tensorModel_right_congruence σ H K u a ha)
  obtain ⟨s, hs, _⟩ := Weighted.Construction.weighted_unitary_splitting_ultra σ H K c
    (TensorFrameCoordinates.Construction.symplecticFrame_continuous σ H K c hF hEmbedding).2 hF hE hEmbedding hQuadratic hne
    ψ hc hu hn characters.quadratic characters.quadratic_kernel K hKdet hK a
    characters.hermitian characters.hermitian_restriction e he
  refine ⟨s, fun g => (hs g).trans ?_⟩
  exact TensorFrameCoordinates.Construction.tensorModelCoordinates_action σ H K c TensorModelCongruences.Construction.swappedTensorIndex u₀ e₀ rfl _ he
    (TensorUnitary.Construction.weightedTensorUnitary σ K a g) (1, g) (TensorModelCongruences.Construction.tensorModel_right_intertwines σ H K u a g)

theorem ultra_dual_pair_splitting
    (hH : DualPair.Construction.adjointMatrix σ H = H) (hK : DualPair.Construction.adjointMatrix σ K = -K)
    (hHdet : H.det ≠ 0) (hKdet : K.det ≠ 0) :
    ∃ splitting : (DualPair.Construction.unitaryGroup σ H × DualPair.Construction.unitaryGroup σ K) →ₜ* Oscillator.Construction.CircleExtension σ H K c ψ,
      ∀ g, Oscillator.Construction.circleProjection σ H K c ψ (splitting g) = DualPair.Construction.continuousDualPairAction σ H K g := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let : IsTopologicalGroup (Oscillator.Construction.CircleExtension σ H K c ψ) :=
    GroupTopology.Construction.circleExtension_isTopologicalGroup hF hEmbedding σ H K c ψ
  obtain ⟨s, hs, hscomm⟩ := ultra_left_factor_splitting σ H K c hF hE hEmbedding hQuadratic hne
    ψ hc hu hn characters hH hK hHdet hKdet
  obtain ⟨t, ht⟩ := ultra_right_factor_splitting σ H K c hF hE hEmbedding hQuadratic hne
    ψ hc hu hn characters hH hK hHdet hKdet
  exact Assembly.Construction.dualPairSplitting_assembly σ H K c ψ s t hs ht hscomm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.UltraFactorSplittings.Construction
