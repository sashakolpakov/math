import OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedCayleyLifts
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyMatrixCoordinates

/-! # Weighted Cayley Multiplication -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedCayleyMultiplication.Construction

noncomputable section

/-! The actual generic weighted tensor lifts have the determinant-character
cocycle required by the given splitting character. -/

open _root_.Matrix _root_.MeasureTheory

theorem weightedRawCayleyLift_multiplication
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
    [CharZero F] [IsUltrametricDist F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace E] [BorelSpace E] {m n p q : ℕ}
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
    (hQuadratic : Module.finrank F E = 2) (hne : ∃ z : E, σ z ≠ z)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (hn : ∃ x : F, ψ x ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))) [ν.IsAddHaarMeasure]
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (Γ : ℂ) (hΓ0 : Γ ≠ 0)
    (hΓ : ∀ t : Fˣ, GaussianCutoff.Construction.HasGaussianCutoffs μE ψ (fun x => (t : F) * Algebra.norm F x) (GaussianCutoffHaar.Construction.normGaussianValue ω Γ t))
    (Q : Matrix (Fin p) (Fin p) E) (hQ : Q.det ≠ 0) (hskew : DualPair.Construction.adjointMatrix σ Q = -Q)
    (a : Fin q → Fˣ) (χ : Eˣ →ₜ* Circle) (hχ : Characters.Construction.HasSplittingRestriction ω q χ)
    (e : (Fin (p * q) → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
    (he : ∀ x y, Oscillator.Construction.standardSymplecticPairing (m * n) (e x) (e y) =
      Algebra.trace F E (DualPair.Construction.sesquilinear σ (TensorUnitary.Construction.weightedTensorForm Q a) x y) / 2)
    (g h : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q) (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    WeightedCayleyLifts.Construction.weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he g *
      WeightedCayleyLifts.Construction.weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he h =
      Oscillator.Construction.circleScalar σ H K c ψ (WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p *
        GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g * GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ h *
          (GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ (g * h))⁻¹) *
        WeightedCayleyLifts.Construction.weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he (g * h) := by
  let : SecondCountableTopology E := TestSpaceAnalysis.Construction.localField_secondCountable E hE
  let G := TensorUnitary.Construction.weightedTensorUnitary σ Q a
  let α := WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he
  let Dg := WeightedCayleyLifts.Construction.weightedFrameDifference σ Q a e g hg
  let Dh := WeightedCayleyLifts.Construction.weightedFrameDifference σ Q a e h hh
  let Dgh := WeightedCayleyLifts.Construction.weightedFrameDifference σ Q a e (g * h) hgh
  have hDg : ∀ v, Dg v = (α g).val v - v := WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he g hg
  have hDh : ∀ v, Dh v = (α h).val v - v := WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he h hh
  have hDgh : ∀ v, Dgh v = (α g * α h).val v - v := by
    intro v
    rw [← map_mul]
    exact WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he (g * h) hgh v
  let μ : Measure (Fin (p * q) → E) := ν.map e.symm.toContinuousAddEquiv
  let : μ.IsAddHaarMeasure := e.symm.toContinuousAddEquiv.isAddHaarMeasure_map ν
  let : μ.Regular := Measure.Regular.map e.symm.toHomeomorph
  obtain ⟨Z, hZ, hcut, hphase⟩ := WeightedTensorGaussian.Construction.weightedTensor_hasGaussianCutoffs hE hQuadratic σ hne ω hω
    μE ψ Γ hΓ0 hΓ μ Q hQ hskew a χ hχ g h hg hh hgh
  let A := GaussianDiscriminant.Construction.unitaryProductGaussianMatrix σ (TensorUnitary.Construction.weightedTensorForm Q a) (G g) (G h)
  have ht := hcut.transport e.symm.toContinuousAddEquiv ν ψ (HermitianNormForms.Construction.hermitianTraceQuadratic σ A) Z
  have hGgh : G g * G h ∈ Generic.Construction.unitaryGenericDomain σ (TensorUnitary.Construction.weightedTensorForm Q a) := by
    rw [← map_mul]
    exact TensorUnitary.Construction.weightedTensorUnitary_generic σ Q a (g * h) hgh
  have hcoord (x : Fin (p * q) → E) :
      CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F (m * n)) Dg.toLinearEquiv (e x) +
        CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F (m * n)) Dh.toLinearEquiv (e x) =
          HermitianNormForms.Construction.hermitianTraceQuadratic σ A x :=
    CayleyMatrixCoordinates.Construction.cayleyWeylPhase_unitary_sum_coordinates σ (TracePairing.Construction.quadratic_automorphism_involutive hQuadratic σ)
      (TensorUnitary.Construction.weightedTensorForm Q a) (TensorUnitary.Construction.weightedTensorForm_nondegenerate Q hQ a) (TensorUnitary.Construction.weightedTensorForm_skew σ Q hskew a)
      (G g) (G h) (TensorUnitary.Construction.weightedTensorUnitary_generic σ Q a g hg) (TensorUnitary.Construction.weightedTensorUnitary_generic σ Q a h hh) hGgh
      (StandardTransvections.Construction.standardSymplecticBilinear F (m * n)) e he Dg.toLinearEquiv Dh.toLinearEquiv
      (MatrixFrameAction.Construction.matrixFrameDifference_coordinates σ (TensorUnitary.Construction.weightedTensorForm Q a) e (G g) _)
      (MatrixFrameAction.Construction.matrixFrameDifference_coordinates σ (TensorUnitary.Construction.weightedTensorForm Q a) e (G h) _) x
  have hfun : (fun v => HermitianNormForms.Construction.hermitianTraceQuadratic σ A (e.symm.toContinuousAddEquiv v)) =
      fun v => CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F (m * n)) Dg.toLinearEquiv v +
        CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F (m * n)) Dh.toLinearEquiv v := by
    funext v
    have hv := hcoord (e.symm v)
    rw [e.apply_symm_apply] at hv
    exact hv.symm
  rw [hfun] at ht
  have hraw := CanonicalCayleyLift.Construction.ultraCayleyLift_multiplication σ H K c hF ψ hc hu hn ν (α g) (α h)
    Dg.toLinearEquiv Dh.toLinearEquiv Dgh.toLinearEquiv hDg hDh hDgh Z hZ ht
  have hz : DiagonalNormGaussian.Construction.gaussianCircle Z hZ = WeightedTensorGaussian.Construction.tensorWeilConstant ω Γ hΓ0 a p *
      GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ g * GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ h *
        (GenericDeterminantCharacter.Construction.genericDeterminantCharacter σ Q χ (g * h))⁻¹ := Subtype.ext hphase
  have hL := CanonicalCayleyLift.Construction.ultraCayleyLift_congr σ H K c hF ψ hc hu hn ν (α g * α h) (α (g * h))
    Dgh.toLinearEquiv hDgh (WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he (g * h) hgh) (map_mul α g h).symm
  rw [hz, hL] at hraw
  rw [WeightedCayleyLifts.Construction.weightedRawCayleyLift_apply σ H K c hF ψ hc hu hn ν Q a e he g hg,
    WeightedCayleyLifts.Construction.weightedRawCayleyLift_apply σ H K c hF ψ hc hu hn ν Q a e he h hh,
    WeightedCayleyLifts.Construction.weightedRawCayleyLift_apply σ H K c hF ψ hc hu hn ν Q a e he (g * h) hgh]
  exact hraw

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedCayleyMultiplication.Construction
