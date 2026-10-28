import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyEnergyDeterminant
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCanonicalCayley
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak

/-! # Real Cayley Continuity -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyContinuity.Construction

noncomputable section

/-! Canonical real Cayley lifts vary continuously in the actual circle extension. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

theorem realWeakGaussian_family_continuous
    {P : Type} [TopologicalSpace P] [FirstCountableTopology P] {d : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d)) [ν.IsAddHaarMeasure]
    (q : P → Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d → ℝ) (hq : Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ d => q z.1 z.2))
    (f k : Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ d) :
    Continuous (fun p => WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν (q p) f.val k.val) := by
  obtain ⟨C, hC⟩ := RealWeylCoefficients.Construction.exists_real_weyl_coefficient_schwartz ψ hc hu hn (Weak.Construction.referencePositionMeasure ℝ d) f k
  have heq : (fun p => WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ d) ν (q p) f.val k.val) =
      (fun p => ∫ v, ψ (q p v) * C v ∂ν) := by
    funext p
    unfold WeakWeylGaussian.Construction.weakWeylGaussian
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      dsimp only
      rw [hC]
  rw [heq]
  apply continuous_of_dominated (bound := fun v => ‖C v‖)
  · intro p
    exact (((hc.comp hq).comp (continuous_const.prodMk continuous_id)).mul C.continuous).aestronglyMeasurable
  · intro p
    exact Filter.Eventually.of_forall fun v => by rw [norm_mul, hu, one_mul]
  · exact C.integrable.norm
  · exact Filter.Eventually.of_forall fun v =>
      (((hc.comp hq).comp (continuous_id.prodMk continuous_const)).mul continuous_const)

theorem realCayleyLift_family_continuous
    {E P : Type} [NormedField E] [Algebra ℝ E] {m n : ℕ}
    [TopologicalSpace P] [FirstCountableTopology P]
    (σ : E ≃ₐ[ℝ] E) (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K)
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t : ℝ => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))) [ν.IsAddHaarMeasure]
    (g : P → FrameTransport.Construction.StandardSymplectic ℝ (m * n))
    (D : P → Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n) ≃L[ℝ] Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n))
    (hD : ∀ p x, D p x = (g p).val x - x)
    (hDc : Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n) => D z.1 z.2))
    (hDi : Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n) => (D z.1).symm z.2))
    (hp : Continuous (fun p => FrameTransport.Construction.frameSymplectic σ H K c (g p))) :
    Continuous (fun p => RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p)) := by
  let a := fun p => RealCayleyLift.Construction.realCayleyLift σ H K c ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p)
  let r := fun p => RealCayleyLift.Construction.realCayleyLiftRadius σ H K c ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p)
  have hspec (p : P) := RealCayleyLift.Construction.realCayleyLift_spec σ H K c ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p)
  obtain ⟨s, -, hs⟩ := RealCayleyEnergyDeterminant.Construction.realCayleyOperator_energy_determinant ψ hc hu hn ν
  obtain ⟨u, hu0⟩ := LocalTest.Construction.exists_test_nonzero_of_real_coordinates (ContinuousAddEquiv.refl (Local.FunctionsMetaplectic.Construction.Position ℝ (m * n)))
  have huE : Local.FunctionsMetaplectic.Construction.l2Energy ℝ (m * n) u ≠ 0 := (Weak.Construction.l2Energy_eq_zero_iff ℝ (m * n) u).not.mpr hu0
  have hrsq (p : P) : (r p) ^ 2 = s * |LinearMap.det (D p).toLinearEquiv.toLinearMap| := by
    have hh := hs (g p) (D p).toLinearEquiv (hD p) u
    rw [(hspec p).2.2, FourierPairing.Construction.l2Energy_smul, (a p).property.1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hspec p).1] at hh
    exact mul_right_cancel₀ huE hh
  have hre : r = fun p => Real.sqrt (s * |(D p).toContinuousLinearMap.det|) := by
    funext p
    change r p = Real.sqrt (s * |LinearMap.det (D p).toLinearEquiv.toLinearMap|)
    rw [← hrsq p, Real.sqrt_sq (hspec p).1.le]
  have hDclm : Continuous (fun p => (D p).toContinuousLinearMap) := by
    apply continuous_clm_apply.mpr
    intro v
    exact hDc.comp (continuous_id.prodMk continuous_const)
  have hrc : Continuous r := by
    rw [hre]
    exact (continuous_const.mul (ContinuousLinearMap.continuous_det.comp hDclm).abs).sqrt
  let q := fun p => CayleyCompositionPhase.Construction.cayleyWeylPhase (StandardTransvections.Construction.standardSymplecticBilinear ℝ (m * n)) (D p).toLinearEquiv
  have hqc : Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n) => q z.1 z.2) := by
    change Continuous (fun z : P × Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (m * n) =>
      BilinearFourierCoordinates.Construction.finiteBilinearContinuous (StandardTransvections.Construction.standardSymplecticBilinear ℝ (m * n)) ((D z.1).symm z.2) z.2 / 2)
    fun_prop
  apply Weak.Construction.circleExtension_continuous_of_weak σ H K c ψ a
  · have heq : (fun p => Oscillator.Construction.circleProjection σ H K c ψ (a p)) =
        fun p => FrameTransport.Construction.frameSymplectic σ H K c (g p) := funext fun p => (hspec p).2.1
    rw [heq]
    exact hp
  · intro f k
    have heq : (fun p => ⟪Weak.Construction.testToL2 ℝ (m * n) k, Weak.Construction.testToL2 ℝ (m * n) ((a p).val.2 f)⟫_ℂ) =
        fun p => (r p : ℂ)⁻¹ * WeakWeylGaussian.Construction.weakWeylGaussian ψ (Weak.Construction.referencePositionMeasure ℝ (m * n)) ν (q p) f.val k.val := by
      funext p
      rw [← RealCayleyOperator.Construction.realCayleyOperator_pairing ψ hc hu hn ν (g p) (D p).toLinearEquiv (hD p),
        (hspec p).2.2, map_smul, inner_smul_right, ← mul_assoc,
        inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hspec p).1.ne'), one_mul]
    rw [heq]
    exact ((Complex.continuous_ofReal.comp hrc).inv₀
      (fun p => Complex.ofReal_ne_zero.mpr (hspec p).1.ne')).mul
      (realWeakGaussian_family_continuous ψ hc hu hn ν q hqc f k)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCayleyContinuity.Construction
