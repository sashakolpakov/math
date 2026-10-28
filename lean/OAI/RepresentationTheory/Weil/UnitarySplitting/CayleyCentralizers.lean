import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianCovariance
import OAI.RepresentationTheory.Weil.UnitarySplitting.PositiveCommutation
import OAI.RepresentationTheory.Weil.UnitarySplitting.CanonicalCayleyLift

/-! # Cayley Centralizers -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCentralizers.Construction

noncomputable section

/-! Canonical Cayley lifts commute with every oscillator lift of a
symplectic transformation centralizing their projection. -/

open _root_.MeasureTheory
open scoped InnerProductSpace NNReal

theorem ultraCayleyOperator_positive_commutation
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [IsUltrametricDist F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
    (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic F d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F d ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (hD : ∀ x, D x = g.val x - x) (k : FrameTransport.Construction.StandardSymplectic F d)
    (hcomm : ∀ x, g.val (k.val x) = k.val (g.val x))
    (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hU : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (hcov : ∀ v f, U (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (k.val v) (U f)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f, (c : ℂ) • UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g D hD (U f) =
      U (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g D hD f) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let κ := k.val.toContinuousLinearEquiv
    let μ : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F d) := ν.map κ
    let : μ.IsAddHaarMeasure := κ.toContinuousAddEquiv.isAddHaarMeasure_map ν
    let : μ.Regular := Measure.Regular.map κ.toHomeomorph
    let c := Measure.addHaarScalarFactor μ ν
    have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
    have hμ : ν.map κ = c • ν := Measure.isAddLeftInvariant_eq_smul_of_regular μ ν
    let q := CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear F d) D
    have hq : ∀ v, q (κ v) = q v := PositiveCommutation.Construction.cayleyWeylPhase_centralizer
      (StandardTransvections.Construction.standardSymplecticBilinear F d) g.val D k.val hD k.property hcomm
    refine ⟨c, hcpos, fun f => ?_⟩
    apply UltraCayleyOperator.Construction.testPairing_ext
    intro h
    obtain ⟨h, rfl⟩ := U.surjective h
    have hUi : ⟪Weak.Construction.testToL2 F d (U h), Weak.Construction.testToL2 F d
        (U (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g D hD f))⟫_ℂ =
        ⟪Weak.Construction.testToL2 F d h, Weak.Construction.testToL2 F d (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g D hD f)⟫_ℂ :=
      Weak.Construction.energy_preserving_inner F d U.toLinearMap hU h (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g D hD f)
    rw [map_smul, inner_smul_right, UltraCayleyOperator.Construction.ultraCayleyOperator_pairing, hUi, UltraCayleyOperator.Construction.ultraCayleyOperator_pairing]
    exact WeakGaussianCovariance.Construction.weakWeylGaussian_covariance hF ψ hc hu ν κ c hμ q hq U hU hcov f h

theorem ultraCayleyLift_centralizer
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E] {m n : ℕ}
    [CompleteSpace F] [LocallyCompactSpace F] [CharZero F] [IsUltrametricDist F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (σ : E ≃ₐ[F] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (hF : ¬ DiscreteTopology F)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (hn : ∃ x : F, ψ x ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic F (m * n)) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n) ≃ₗ[F] Local.FunctionsMetaplectic.Construction.PhaseSpace F (m * n))
    (hD : ∀ x, D x = g.val x - x) (k : FrameTransport.Construction.StandardSymplectic F (m * n))
    (hcomm : ∀ x, g.val (k.val x) = k.val (g.val x))
    (b : Oscillator.Construction.CircleExtension σ H K c ψ)
    (hb : Oscillator.Construction.circleProjection σ H K c ψ b = FrameTransport.Construction.frameSymplectic σ H K c k) :
    Commute (CanonicalCayleyLift.Construction.ultraCayleyLift σ H K c hF ψ hc hu hn ν g D hD) b := by
  let a := CanonicalCayleyLift.Construction.ultraCayleyLift σ H K c hF ψ hc hu hn ν g D hD
  obtain ⟨hr, hp, hM⟩ := CanonicalCayleyLift.Construction.ultraCayleyLift_spec σ H K c hF ψ hc hu hn ν g D hD
  obtain ⟨s, hs, hMs⟩ := ultraCayleyOperator_positive_commutation hF ψ hc hu hn ν g D hD k hcomm
    b.val.2 b.property.1 (UltraCayleyLift.Construction.frameLift_heisenberg_covariance σ H K c hF ψ hc hu k b hb)
  have hop := PositiveCommutation.Construction.positive_operator_commutation (UltraCayleyOperator.Construction.ultraCayleyOperator hF ψ hc hu hn ν g D hD) a.val.2 b.val.2
    a.property.1 b.property.1 (LocalTest.Construction.ultraTestVector F hF (m * n)) (LocalTest.Construction.ultraTestVector_ne_zero F hF (m * n))
    (CanonicalCayleyLift.Construction.ultraCayleyLiftRadius σ H K c hF ψ hc hu hn ν g D hD) hr hM s hs hMs
  change a * b = b * a
  apply Subtype.ext
  apply Prod.ext
  · have hpa : a.val.1 = FrameTransport.Construction.frameSymplectic σ H K c g := hp
    have hpb : b.val.1 = FrameTransport.Construction.frameSymplectic σ H K c k := hb
    change a.val.1 * b.val.1 = b.val.1 * a.val.1
    rw [hpa, hpb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact hcomm x
  · apply LinearEquiv.ext
    intro f
    exact hop f

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCentralizers.Construction
