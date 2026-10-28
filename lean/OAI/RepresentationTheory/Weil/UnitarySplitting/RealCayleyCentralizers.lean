import OAI.RepresentationTheory.Weil.UnitarySplitting.WeakGaussianCovariance
import OAI.RepresentationTheory.Weil.UnitarySplitting.PositiveCommutation
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCanonicalCayley

/-! # Real Cayley Centralizers -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyCentralizers.Construction

noncomputable section

/-! Canonical Cayley lifts commute with every oscillator lift of a
symplectic transformation centralizing their projection. -/

open _root_.MeasureTheory
open scoped InnerProductSpace NNReal

theorem realCayleyOperator_positive_commutation
    {d : ℕ} (ψ : AddChar ℝ ℂ)
    (hc : Continuous (fun x : ℝ => ψ x)) (hu : ∀ x : ℝ, ‖ψ x‖ = 1) (hn : ∃ x : ℝ, ψ x ≠ 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic ℝ d) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)
    (hD : ∀ x, D x = g.val x - x) (k : FrameTransport.Construction.StandardSymplectic ℝ d)
    (hcomm : ∀ x, g.val (k.val x) = k.val (g.val x))
    (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d)
    (hU : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy ℝ d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy ℝ d f)
    (hcov : ∀ v f, U (HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu v f) =
      HeisenbergStability.Construction.heisenbergOperator RealFourierUnitary.Construction.real_nondiscrete ψ hc hu (k.val v) (U f)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f, (c : ℂ) • RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD (U f) =
      U (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD f) := by
  let κ := k.val.toContinuousLinearEquiv
  let μ : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d) := ν.map κ
  let : μ.IsAddHaarMeasure := κ.toContinuousAddEquiv.isAddHaarMeasure_map ν
  let : μ.Regular := Measure.Regular.map κ.toHomeomorph
  let c := Measure.addHaarScalarFactor μ ν
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν
  have hμ : ν.map κ = c • ν := Measure.isAddLeftInvariant_eq_smul_of_regular μ ν
  let q := CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) D
  have hq : ∀ v, q (κ v) = q v := PositiveCommutation.Construction.cayleyWeylPhase_centralizer
    (StandardTransvections.Construction.standardSymplecticBilinear ℝ d) g.val D k.val hD k.property hcomm
  refine ⟨c, hcpos, fun f => ?_⟩
  apply UltraCayleyOperator.Construction.testPairing_ext
  intro h
  obtain ⟨h, rfl⟩ := U.surjective h
  have hUi : ⟪Weak.Construction.testToL2 ℝ d (U h), Weak.Construction.testToL2 ℝ d
      (U (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD f))⟫_ℂ =
      ⟪Weak.Construction.testToL2 ℝ d h, Weak.Construction.testToL2 ℝ d (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD f)⟫_ℂ :=
    Weak.Construction.energy_preserving_inner ℝ d U.toLinearMap hU h (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD f)
  rw [map_smul, inner_smul_right, RealCayleyOperator.Construction.realCayleyOperator_pairing, hUi, RealCayleyOperator.Construction.realCayleyOperator_pairing]
  exact WeakGaussianCovariance.Construction.weakWeylGaussian_covariance RealFourierUnitary.Construction.real_nondiscrete ψ hc hu ν κ c hμ q hq U hU hcov f h

theorem realCayleyLift_centralizer
    {E : Type} [NormedField E] [Algebra ℝ E] {m n : ℕ}
    (σ : E ≃ₐ[ℝ] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K)
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun x : ℝ => ψ x)) (hu : ∀ x : ℝ, ‖ψ x‖ = 1)
    (hn : ∃ x : ℝ, ψ x ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))) [ν.IsAddHaarMeasure]
    (g : FrameTransport.Construction.StandardSymplectic ℝ (m * n)) (D : Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n) ≃ₗ[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))
    (hD : ∀ x, D x = g.val x - x) (k : FrameTransport.Construction.StandardSymplectic ℝ (m * n))
    (hcomm : ∀ x, g.val (k.val x) = k.val (g.val x))
    (b : Oscillator.Construction.CircleExtension σ H K c ψ)
    (hb : Oscillator.Construction.circleProjection σ H K c ψ b = FrameTransport.Construction.frameSymplectic σ H K c k) :
    Commute (RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν g D hD) b := by
  let a := RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν g D hD
  obtain ⟨hr, hp, hM⟩ := RealCayleyLift.Construction.realCayleyLift_spec σ H K c ψ hc hu hn ν g D hD
  obtain ⟨s, hs, hMs⟩ := realCayleyOperator_positive_commutation ψ hc hu hn ν g D hD k hcomm
    b.val.2 b.property.1 (UltraCayleyLift.Construction.frameLift_heisenberg_covariance σ H K c RealFourierUnitary.Construction.real_nondiscrete ψ hc hu k b hb)
  obtain ⟨u, hu0⟩ := LocalTest.Construction.exists_test_nonzero_of_real_coordinates (ContinuousAddEquiv.refl (Local.FunctionsMetaplectic.Construction.Position ℝ (m * n)))
  have hop := PositiveCommutation.Construction.positive_operator_commutation (RealCayleyOperator.Construction.realCayleyOperator ψ hc hu hn ν g D hD) a.val.2 b.val.2
    a.property.1 b.property.1 u hu0
    (RealCayleyLift.Construction.realCayleyLiftRadius σ H K c ψ hc hu hn ν g D hD) hr hM s hs hMs
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

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyCentralizers.Construction
