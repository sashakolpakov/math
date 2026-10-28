import OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseMeasure
import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner

/-! # Phase Fourier -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseFourier.Construction

noncomputable section

/-! The Fourier transform for the Schrödinger alternating pairing is the
coordinate Fourier transform followed by a measure-preserving rotation. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner.LocalAnalysis _root_.MeasureTheory

variable (k : Type) [NormedField k] (N : ℕ)

theorem phaseCoordinates_dot (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    Local.FunctionsMetaplectic.Construction.dot (PhaseMeasure.Construction.phaseCoordinates k N v) (PhaseMeasure.Construction.phaseCoordinates k N w) = ∑ i, v i * w i := by
  simpa [Local.FunctionsMetaplectic.Construction.dot, PhaseMeasure.Construction.phaseCoordinates, ContinuousLinearEquiv.piCongrLeft,
    LinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply] using
    (finSumFinEquiv.symm.sum_comp (fun i => v i * w i))

theorem schrodingerPairing_fourier_frequency (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    SchrodingerPairing.Construction.schrodingerPairing k N v w =
      -Local.FunctionsMetaplectic.Construction.dot (-(PhaseMeasure.Construction.phaseCoordinates k N (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k N) v)))
        (PhaseMeasure.Construction.phaseCoordinates k N w) := by
  have hn (x y : Local.FunctionsMetaplectic.Construction.Position k (N + N)) : Local.FunctionsMetaplectic.Construction.dot (-x) y = -Local.FunctionsMetaplectic.Construction.dot x y := by
    simp [Local.FunctionsMetaplectic.Construction.dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [hn, neg_neg, phaseCoordinates_dot, SchrodingerPairing.Construction.schrodingerPairing_eq_standard]
  simp [Local.FunctionsMetaplectic.Construction.symplecticAction, Local.Generators.Construction.weylSymplectic_matrix, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply,
    UnitarySplitting.Oscillator.Construction.standardSymplecticPairing, sub_eq_add_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]

variable [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]

omit [LocallyCompactSpace k] in
theorem phaseFourier_coordinate_formula (ψ : AddChar k ℂ)
    (μ : Measure k) [SigmaFinite μ] (f : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ) (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k N) :
    (∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N v w) * f w ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) =
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ))
        (fun x => f ((PhaseMeasure.Construction.phaseCoordinates k N).symm x))
        (-(PhaseMeasure.Construction.phaseCoordinates k N (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k N) v))) := by
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← (PhaseMeasure.Construction.phaseCoordinates_measurePreserving k N μ).integral_comp
    (PhaseMeasure.Construction.phaseCoordinates k N).toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    dsimp only
    rw [ContinuousLinearEquiv.symm_apply_apply, schrodingerPairing_fourier_frequency]
    exact mul_comm _ _

theorem phaseFourier_norm_sq_of_coordinate (ψ : AddChar k ℂ)
    (μ : Measure k) [μ.IsAddHaarMeasure]
    (f : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ)
    (hP : (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ))
        (fun y => f ((PhaseMeasure.Construction.phaseCoordinates k N).symm y)) x‖ ^ 2
        ∂Measure.pi (fun _ : Fin (N + N) => μ)) =
      ∫ x, ‖f ((PhaseMeasure.Construction.phaseCoordinates k N).symm x)‖ ^ 2 ∂Measure.pi (fun _ : Fin (N + N) => μ)) :
    (∫ v, ‖∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N v w) * f w
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) =
      ∫ v, ‖f v‖ ^ 2 ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ) := by
  let F := Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ))
    (fun x => f ((PhaseMeasure.Construction.phaseCoordinates k N).symm x))
  let E : Local.FunctionsMetaplectic.Construction.PhaseSpace k N ≃ₜ Local.FunctionsMetaplectic.Construction.PhaseSpace k N :=
    { __ := (SchrodingerPairing.Construction.symplecticPhaseEquiv k N (Local.Generators.Construction.weylSymplectic k N)).toEquiv
      continuous_toFun := LinearMap.continuous_on_pi
        (SchrodingerPairing.Construction.symplecticPhaseEquiv k N (Local.Generators.Construction.weylSymplectic k N)).toLinearMap
      continuous_invFun := LinearMap.continuous_on_pi
        (SchrodingerPairing.Construction.symplecticPhaseEquiv k N (Local.Generators.Construction.weylSymplectic k N)).symm.toLinearMap }
  simp_rw [phaseFourier_coordinate_formula]
  change (∫ v, ‖F (-(PhaseMeasure.Construction.phaseCoordinates k N (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k N) v)))‖ ^ 2
    ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) = _
  rw [(PhaseMeasure.Construction.symplecticAction_measurePreserving k N μ (Local.Generators.Construction.weylSymplectic k N)).integral_comp
    E.measurableEmbedding (fun v => ‖F (-(PhaseMeasure.Construction.phaseCoordinates k N v))‖ ^ 2)]
  rw [(PhaseMeasure.Construction.phaseCoordinates_measurePreserving k N μ).integral_comp
    (PhaseMeasure.Construction.phaseCoordinates k N).toHomeomorph.measurableEmbedding (fun x => ‖F (-x)‖ ^ 2)]
  rw [integral_neg_eq_self (fun x => ‖F x‖ ^ 2)]
  have hp := hP
  change (∫ x, ‖F x‖ ^ 2 ∂Measure.pi (fun _ : Fin (N + N) => μ)) = _ at hp
  rw [hp, ← (PhaseMeasure.Construction.phaseCoordinates_measurePreserving k N μ).integral_comp
    (PhaseMeasure.Construction.phaseCoordinates k N).toHomeomorph.measurableEmbedding]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

theorem phaseFourier_norm_sq (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
    (μ : Measure k) [μ.IsAddHaarMeasure]
    (hStable : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N),
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ)) f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N))
    (hInv : ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N)) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ))
        (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ)) f.val) x = f.val (-x))
    (f : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ)
    (hf : (fun x => f ((PhaseMeasure.Construction.phaseCoordinates k N).symm x)) ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N)) :
    (∫ v, ‖∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N v w) * f w
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)‖ ^ 2
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) =
      ∫ v, ‖f v‖ ^ 2 ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ) :=
  phaseFourier_norm_sq_of_coordinate k N ψ μ f
    (FourierIntertwiner.LocalAnalysis.fourierIntegral_norm_sq ψ hu hc (Measure.pi (fun _ : Fin (N + N) => μ))
      hStable hInv (⟨_, hf⟩ : Local.FunctionsMetaplectic.Construction.schwartzBruhat k (N + N)))

theorem phaseFourier_continuous (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
    (μ : Measure k) [μ.IsAddHaarMeasure] (f : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ)
    (hf : Integrable f (Measure.pi (fun _ : Fin N ⊕ Fin N => μ))) :
    Continuous (fun v => ∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N v w) * f w
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) := by
  let e := (PhaseMeasure.Construction.phaseCoordinates k N).toHomeomorph.toMeasurableEquiv
  have hp := PhaseMeasure.Construction.phaseCoordinates_measurePreserving k N μ
  have hi : Integrable (f ∘ (PhaseMeasure.Construction.phaseCoordinates k N).symm)
      (Measure.pi (fun _ : Fin (N + N) => μ)) := (hp.symm e).integrable_comp_of_integrable hf
  have hF := FourierTools.LocalAnalysis.fourierIntegral_continuous ψ hu hc (Measure.pi (fun _ : Fin (N + N) => μ)) hi
  have he : (fun v => ∫ w, ψ (SchrodingerPairing.Construction.schrodingerPairing k N v w) * f w
      ∂Measure.pi (fun _ : Fin N ⊕ Fin N => μ)) =
    fun v => Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin (N + N) => μ))
      (f ∘ (PhaseMeasure.Construction.phaseCoordinates k N).symm)
      (-(PhaseMeasure.Construction.phaseCoordinates k N (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k N) v))) :=
    funext (phaseFourier_coordinate_formula k N ψ μ f)
  rw [he]
  apply hF.comp
  apply Continuous.neg
  apply (PhaseMeasure.Construction.phaseCoordinates k N).continuous.comp
  exact LinearMap.continuous_on_pi (Matrix.toLin' (Local.Generators.Construction.weylSymplectic k N).val)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseFourier.Construction
