import OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedCayleyLifts
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyContinuity

/-! # Weighted Real Cayley Lifts -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedRealCayleyLifts.Construction

noncomputable section

/-! Canonical real Cayley lifts for weighted tensor unitary actions. -/

open _root_.Matrix _root_.MeasureTheory

variable {E : Type} [NormedField E] [Algebra ℝ E] {m n p q : ℕ}
variable (σ : E ≃ₐ[ℝ] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
variable (c : Oscillator.Construction.SymplecticFrame σ H K)
variable (ψ : AddChar ℝ ℂ) (hc : Continuous (fun x : ℝ => ψ x)) (hu : ∀ x : ℝ, ‖ψ x‖ = 1)
variable (hn : ∃ x : ℝ, ψ x ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))) [ν.IsAddHaarMeasure]
variable (Q : Matrix (Fin p) (Fin p) E) (a : Fin q → ℝˣ)
variable (e : (Fin (p * q) → E) ≃L[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))
variable (he : ∀ x y, Oscillator.Construction.standardSymplecticPairing (m * n) (e x) (e y) =
  Algebra.trace ℝ E (DualPair.Construction.sesquilinear σ (TensorUnitary.Construction.weightedTensorForm Q a) x y) / 2)

def weightedRealCayleyLiftOnGeneric (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    Oscillator.Construction.CircleExtension σ H K c ψ :=
  RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν (WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g)
    (WeightedCayleyLifts.Construction.weightedFrameDifference σ Q a e g hg).toLinearEquiv (WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he g hg)

def weightedRealRawCayleyLift (g : DualPair.Construction.unitaryGroup σ Q) : Oscillator.Construction.CircleExtension σ H K c ψ := by
  classical
  exact if hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q then
    weightedRealCayleyLiftOnGeneric σ H K c ψ hc hu hn ν Q a e he g hg else 1

theorem weightedRealRawCayleyLift_apply (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    weightedRealRawCayleyLift σ H K c ψ hc hu hn ν Q a e he g =
      weightedRealCayleyLiftOnGeneric σ H K c ψ hc hu hn ν Q a e he g hg := by
  simp only [weightedRealRawCayleyLift, dite_eq_left hg]

theorem weightedRealRawCayleyLift_projection (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    Oscillator.Construction.circleProjection σ H K c ψ (weightedRealRawCayleyLift σ H K c ψ hc hu hn ν Q a e he g) =
      FrameTransport.Construction.frameSymplectic σ H K c (WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g) := by
  rw [weightedRealRawCayleyLift_apply σ H K c ψ hc hu hn ν Q a e he g hg]
  exact (RealCayleyLift.Construction.realCayleyLift_spec σ H K c ψ hc hu hn ν (WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g)
    (WeightedCayleyLifts.Construction.weightedFrameDifference σ Q a e g hg).toLinearEquiv (WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he g hg)).2.1

theorem weightedRealRawCayleyLift_continuousOn (hci : Continuous c.coordinates.symm) :
    ContinuousOn (weightedRealRawCayleyLift σ H K c ψ hc hu hn ν Q a e he) (Generic.Construction.unitaryGenericDomain σ Q) := by
  let : FirstCountableTopology (Matrix (Fin p) (Fin p) E) :=
    inferInstanceAs (FirstCountableTopology (Fin p → Fin p → E))
  let : FirstCountableTopology (Matrix (Fin p) (Fin p) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.firstCountableTopology
  let : FirstCountableTopology (Matrix (Fin p) (Fin p) E)ˣ :=
    Units.isInducing_embedProduct.firstCountableTopology
  let : FirstCountableTopology (DualPair.Construction.unitaryGroup σ Q) :=
    TopologicalSpace.firstCountableTopology_induced _ (Matrix (Fin p) (Fin p) E)ˣ Subtype.val
  let P := ↥(Generic.Construction.unitaryGenericDomain σ Q)
  let : FirstCountableTopology P :=
    TopologicalSpace.firstCountableTopology_induced P (DualPair.Construction.unitaryGroup σ Q) Subtype.val
  let G : P → DualPair.Construction.unitaryGroup σ (TensorUnitary.Construction.weightedTensorForm Q a) := fun g => TensorUnitary.Construction.weightedTensorUnitary σ Q a g.val
  have hGc : Continuous G := (TensorModelTopology.Construction.weightedTensorUnitary_continuous σ Q a).comp continuous_subtype_val
  have hGg (g : P) : G g ∈ Generic.Construction.unitaryGenericDomain σ (TensorUnitary.Construction.weightedTensorForm Q a) :=
    TensorUnitary.Construction.weightedTensorUnitary_generic σ Q a g.val g.property
  obtain ⟨hDc, hDi⟩ := MatrixFrameAction.Construction.matrixFrameDifference_family_continuous σ (TensorUnitary.Construction.weightedTensorForm Q a) e G hGg hGc
  have hp : Continuous (fun g : P => FrameTransport.Construction.frameSymplectic σ H K c (WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g.val)) :=
    (TensorModelTopology.Construction.frameSymplectic_continuous σ H K c hci).comp
      ((MatrixFrameAction.Construction.matrixFrameAction_continuous σ (TensorUnitary.Construction.weightedTensorForm Q a) e he).comp hGc)
  have hcont : Continuous (fun g : P => weightedRealCayleyLiftOnGeneric σ H K c ψ hc hu hn ν Q a e he g.val g.property) :=
    RealCayleyContinuity.Construction.realCayleyLift_family_continuous σ H K c ψ hc hu hn ν
      (fun g : P => WeightedCayleyLifts.Construction.weightedFrameAction σ Q a e he g.val)
      (fun g : P => WeightedCayleyLifts.Construction.weightedFrameDifference σ Q a e g.val g.property)
      (fun g : P => WeightedCayleyLifts.Construction.weightedFrameDifference_action σ Q a e he g.val g.property) hDc hDi hp
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun g : P => weightedRealRawCayleyLift σ H K c ψ hc hu hn ν Q a e he g.val)
  convert hcont using 1
  funext g
  exact weightedRealRawCayleyLift_apply σ H K c ψ hc hu hn ν Q a e he g.val g.property

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.WeightedRealCayleyLifts.Construction
