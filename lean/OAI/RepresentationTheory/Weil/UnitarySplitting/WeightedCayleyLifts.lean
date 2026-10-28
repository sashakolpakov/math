import OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedTensorGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.MatrixFrameAction
import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorModelTopology
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyLiftContinuity

/-! # Weighted Cayley Lifts -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedCayleyLifts.Construction

noncomputable section

/-! Actual generic Cayley lifts for a weighted tensor unitary action. -/

open _root_.Matrix _root_.MeasureTheory

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [CharZero F] [IsUltrametricDist F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable {m n p q : ℕ}
variable (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K) (hF : ¬ DiscreteTopology F)
variable (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
variable (hn : ∃ x : F, ψ x ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))) [ν.IsAddHaarMeasure]
variable (Q : Matrix (Fin p) (Fin p) E) (a : Fin q → Fˣ)
variable (e : (Fin (p * q) → E) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
variable (he : ∀ x y, Oscillator.Construction.standardSymplecticPairing (m * n) (e x) (e y) =
  Algebra.trace F E (DualPair.Construction.sesquilinear σ (TensorUnitary.Construction.weightedTensorForm Q a) x y) / 2)

def weightedFrameAction : DualPair.Construction.unitaryGroup σ Q →* FrameTransport.Construction.StandardSymplectic F (m * n) :=
  (MatrixFrameAction.Construction.matrixFrameAction σ (TensorUnitary.Construction.weightedTensorForm Q a) e.toLinearEquiv he).comp (TensorUnitary.Construction.weightedTensorUnitary σ Q a)

def weightedFrameDifference (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) :=
  MatrixFrameAction.Construction.matrixFrameDifference σ (TensorUnitary.Construction.weightedTensorForm Q a) e (TensorUnitary.Construction.weightedTensorUnitary σ Q a g)
    (TensorUnitary.Construction.weightedTensorUnitary_generic σ Q a g hg)

omit [CompleteSpace F] [LocallyCompactSpace F] [CharZero F] [IsUltrametricDist F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem weightedFrameDifference_action (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n)) :
    weightedFrameDifference σ Q a e g hg v = (weightedFrameAction σ Q a e he g).val v - v :=
  MatrixFrameAction.Construction.matrixFrameDifference_action σ (TensorUnitary.Construction.weightedTensorForm Q a) e he _ _ v

def weightedCayleyLiftOnGeneric (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    Oscillator.Construction.CircleExtension σ H K c ψ :=
  CanonicalCayleyLift.Construction.ultraCayleyLift σ H K c hF ψ hc hu hn ν (weightedFrameAction σ Q a e he g)
    (weightedFrameDifference σ Q a e g hg).toLinearEquiv (weightedFrameDifference_action σ Q a e he g hg)

def weightedRawCayleyLift (g : DualPair.Construction.unitaryGroup σ Q) : Oscillator.Construction.CircleExtension σ H K c ψ := by
  classical
  exact if hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q then
    weightedCayleyLiftOnGeneric σ H K c hF ψ hc hu hn ν Q a e he g hg else 1

theorem weightedRawCayleyLift_apply (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he g =
      weightedCayleyLiftOnGeneric σ H K c hF ψ hc hu hn ν Q a e he g hg := by
  simp only [weightedRawCayleyLift, dite_eq_left hg]

theorem weightedRawCayleyLift_projection (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    Oscillator.Construction.circleProjection σ H K c ψ (weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he g) =
      FrameTransport.Construction.frameSymplectic σ H K c (weightedFrameAction σ Q a e he g) := by
  rw [weightedRawCayleyLift_apply σ H K c hF ψ hc hu hn ν Q a e he g hg]
  exact (CanonicalCayleyLift.Construction.ultraCayleyLift_spec σ H K c hF ψ hc hu hn ν (weightedFrameAction σ Q a e he g)
    (weightedFrameDifference σ Q a e g hg).toLinearEquiv (weightedFrameDifference_action σ Q a e he g hg)).2.1

theorem weightedRawCayleyLift_continuousOn (hci : Continuous c.coordinates.symm) :
    ContinuousOn (weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he) (Generic.Construction.unitaryGenericDomain σ Q) := by
  let P := ↥(Generic.Construction.unitaryGenericDomain σ Q)
  let G : P → DualPair.Construction.unitaryGroup σ (TensorUnitary.Construction.weightedTensorForm Q a) := fun g => TensorUnitary.Construction.weightedTensorUnitary σ Q a g.val
  have hGc : Continuous G := (TensorModelTopology.Construction.weightedTensorUnitary_continuous σ Q a).comp continuous_subtype_val
  have hGg (g : P) : G g ∈ Generic.Construction.unitaryGenericDomain σ (TensorUnitary.Construction.weightedTensorForm Q a) :=
    TensorUnitary.Construction.weightedTensorUnitary_generic σ Q a g.val g.property
  obtain ⟨hDc, hDi⟩ := MatrixFrameAction.Construction.matrixFrameDifference_family_continuous σ (TensorUnitary.Construction.weightedTensorForm Q a) e G hGg hGc
  have hp : Continuous (fun g : P => FrameTransport.Construction.frameSymplectic σ H K c (weightedFrameAction σ Q a e he g.val)) :=
    (TensorModelTopology.Construction.frameSymplectic_continuous σ H K c hci).comp
      ((MatrixFrameAction.Construction.matrixFrameAction_continuous σ (TensorUnitary.Construction.weightedTensorForm Q a) e he).comp hGc)
  have hcont : Continuous (fun g : P => weightedCayleyLiftOnGeneric σ H K c hF ψ hc hu hn ν Q a e he g.val g.property) :=
    CayleyLiftContinuity.Construction.ultraCayleyLift_family_continuous σ H K c hF ψ hc hu hn ν
      (fun g : P => weightedFrameAction σ Q a e he g.val)
      (fun g : P => weightedFrameDifference σ Q a e g.val g.property)
      (fun g : P => weightedFrameDifference_action σ Q a e he g.val g.property) hDc hDi hp
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun g : P => weightedRawCayleyLift σ H K c hF ψ hc hu hn ν Q a e he g.val)
  convert hcont using 1
  funext g
  exact weightedRawCayleyLift_apply σ H K c hF ψ hc hu hn ν Q a e he g.val g.property

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedCayleyLifts.Construction
