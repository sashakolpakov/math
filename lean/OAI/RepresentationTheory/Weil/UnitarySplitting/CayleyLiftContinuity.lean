import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyOperatorFamilies
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormalizedOperatorFamilies
import OAI.RepresentationTheory.Weil.UnitarySplitting.CanonicalCayleyLift

/-! # Cayley Lift Continuity -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyLiftContinuity.Construction

noncomputable section

/-! Continuity of canonical nonarchimedean Cayley lifts in the actual
strong operator topology, including inverse observations. -/

open _root_.MeasureTheory

theorem circleExtension_continuous_of_locallyConstant_operators
    {F E P : Type} [NormedField F] [NormedField E] [Algebra F E] {m n : ℕ}
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F] [TopologicalSpace P]
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ) (a : P → Oscillator.Construction.CircleExtension σ H K c ψ)
    (hp : Continuous (fun p => Oscillator.Construction.circleProjection σ H K c ψ (a p)))
    (ha : ∀ f, IsLocallyConstant (fun p => (a p).val.2 f))
    (hi : ∀ f, IsLocallyConstant (fun p => (a p).val.2.symm f)) : Continuous a := by
  apply continuous_induced_rng.mpr
  apply Continuous.prodMk hp
  apply Continuous.prodMk
  · apply continuous_pi
    rintro ⟨f, k⟩
    exact ((ha f).comp (fun v : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n) => Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (v - k)))).continuous
  · apply continuous_pi
    rintro ⟨f, k⟩
    exact ((hi f).comp (fun v : Local.FunctionsMetaplectic.Construction.schwartzBruhat F (m * n) => Real.sqrt (Local.FunctionsMetaplectic.Construction.l2Energy F (m * n) (v - k)))).continuous

theorem ultraCayleyLift_family_continuous
    {F E P : Type} [NormedField F] [NormedField E] [Algebra F E] {m n : ℕ}
    [CompleteSpace F] [LocallyCompactSpace F] [CharZero F] [IsUltrametricDist F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [TopologicalSpace P]
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (hF : ¬ DiscreteTopology F)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (hn : ∃ x : F, ψ x ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))) [ν.IsAddHaarMeasure]
    (g : P → FrameTransport.Construction.StandardSymplectic F (m * n))
    (D : P → Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) ≃L[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
    (hD : ∀ p x, D p x = (g p).val x - x)
    (hDc : Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) => D z.1 z.2))
    (hDi : Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) => (D z.1).symm z.2))
    (hp : Continuous (fun p => FrameTransport.Construction.frameSymplectic σ H K c (g p))) :
    Continuous (fun p => CanonicalCayleyLift.Construction.ultraCayleyLift σ H K c hF ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p)) := by
  let a := fun p => CanonicalCayleyLift.Construction.ultraCayleyLift σ H K c hF ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p)
  let M := fun p => UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p)
  let r := fun p => CanonicalCayleyLift.Construction.ultraCayleyLiftRadius σ H K c hF ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p)
  have hspec (p : P) := CanonicalCayleyLift.Construction.ultraCayleyLift_spec σ H K c hF ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p)
  obtain ⟨-, hforward, hinverse⟩ := NormalizedOperatorFamilies.Construction.positive_operator_family_locallyConstant M (fun p => (a p).val.2)
    (fun p => (a p).property.1) (LocalTest.Construction.ultraTestVector F hF (m * n)) (LocalTest.Construction.ultraTestVector_ne_zero F hF (m * n))
    r (fun p => (hspec p).1) (fun p => (hspec p).2.2)
    (CayleyOperatorFamilies.Construction.ultraCayleyOperator_family_locallyConstant hF ψ hc hu hn ν g D hD hDc hDi)
  apply circleExtension_continuous_of_locallyConstant_operators σ H K c ψ a _ hforward hinverse
  have heq : (fun p => Oscillator.Construction.circleProjection σ H K c ψ (a p)) =
      fun p => FrameTransport.Construction.frameSymplectic σ H K c (g p) := funext (fun p => (hspec p).2.1)
  rw [heq]
  exact hp

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyLiftContinuity.Construction
