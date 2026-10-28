import OAI.RepresentationTheory.Weil.Local.RealStandardBareKernel
import OAI.RepresentationTheory.Weil.Local.OscillatorRescaling
import OAI.RepresentationTheory.Weil.Local.RealLevi

/-! # Real Bare Kernel -/

namespace OAI.RepresentationTheory.Weil.Local.RealBareKernel.Construction

noncomputable section

section

/-! The actual real bare-kernel sign theorem for every nontrivial unitary character. -/

theorem realCharacter_standard_rescaling (c t : ℝ) : Gaussian.Construction.realCharacter c t = Gaussian.Construction.realCharacter 1 (c * t) := by
  rw [Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply]
  congr 2
  ring_nf

theorem real_metaplectic_kernel_sign {n : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (a : FunctionsMetaplectic.Construction.Metaplectic ℝ n ψ) (ha : FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ a = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n, a.val.val.2 f = ε • f := by
  obtain ⟨c, hc0, rfl⟩ := RealCharacters.Construction.continuous_nontrivial_unitary_real_character ψ hc hu hn
  let b := OscillatorRescaling.Construction.characterRescaleMetaplectic (Gaussian.Construction.realCharacter 1) (Gaussian.Construction.realCharacter c) c hc0
    (realCharacter_standard_rescaling c) a
  have hb : FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter 1) b = 1 := by
    change OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter 1)
      (OscillatorRescaling.Construction.characterRescaleOscillator n (Gaussian.Construction.realCharacter 1) (Gaussian.Construction.realCharacter c) c hc0
        (realCharacter_standard_rescaling c) a.val) = 1
    rw [OscillatorRescaling.Construction.characterRescaleOscillator_projection]
    change Generators.Construction.phaseRescaleSymplectic n c hc0 (FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter c) a) = 1
    rw [ha, map_one]
  exact RealStandardBareKernel.Construction.real_standard_metaplectic_kernel_sign b hb

theorem real_metaplectic_same_projection_sign {n : ℕ}
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (a b : FunctionsMetaplectic.Construction.Metaplectic ℝ n ψ)
    (hab : FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ a = FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ b) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n,
      FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ a f = ε • FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ b f := by
  have hker : FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  obtain ⟨ε, hε, h⟩ := real_metaplectic_kernel_sign ψ hc hu hn (a * b⁻¹) hker
  refine ⟨ε, hε, fun f => ?_⟩
  have hh := h (b.val.val.2 f)
  change a.val.val.2 (b.val.val.2.symm (b.val.val.2 f)) = ε • b.val.val.2 f at hh
  simpa only [LinearEquiv.symm_apply_apply] using! hh

end

/-! All clauses of the repaired LocalWeil theorem at the real place. -/

open _root_.MeasureTheory Filter
open scoped BigOperators _root_.Topology

theorem real_schrodinger_generator_formulas
    (n : ℕ) (hn : 0 < n)
    (ψ : AddChar ℝ ℂ)
    (hContinuous : Continuous (fun t : ℝ => ψ t))
    (hUnitary : ∀ t : ℝ, ‖ψ t‖ = 1)
    (hNontrivial : ∃ t : ℝ, ψ t ≠ 1) :
    -- Positivity prevents the Haar normalization from degenerating.
    (0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ ψ) ∧
    (FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure ∧
    -- The Gaussian phase is taken from an actual nonzero oscillatory limit.
    (∀ a : ℝ, a ≠ 0 →
      Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian ℝ ψ a) (𝓝[>] (0 : ℝ))
        (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral ℝ ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral ℝ ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ a ^ 8 = 1) ∧
    -- The selected Haar measure is self-dual for the coordinate pairing.
    (∀ (φ : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n),
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ) φ.val) x = φ.val (-x)) ∧
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ) ∧
    ∃ (m : FunctionsMetaplectic.Construction.GeneralLinear ℝ n → FunctionsMetaplectic.Construction.Metaplectic ℝ n ψ)
      (u : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n → FunctionsMetaplectic.Construction.Metaplectic ℝ n ψ)
      (w : FunctionsMetaplectic.Construction.Metaplectic ℝ n ψ),
      (∀ A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n,
        FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ (m A) = Generators.Construction.leviSymplectic A) ∧
      (∀ B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n,
        FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ (u B) = Generators.Construction.quadraticSymplectic B) ∧
      FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ w = Generators.Construction.weylSymplectic ℝ n ∧
      (∀ (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) (φ : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ (m A) φ).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ (FunctionsMetaplectic.Construction.determinantUnit ℝ A) / FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ 1) *
          ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus ℝ (FunctionsMetaplectic.Construction.determinantUnit ℝ A)))⁻¹ : ℂ) *
          φ.val (Matrix.mulVec (↑(A⁻¹) : Matrix (Fin n) (Fin n) ℝ) x)) ∧
      (∀ (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) (φ : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ (u B) φ).val x =
          ψ ((∑ i, ∑ j, x i * B.val i j * x j) / 2) * φ.val x) ∧
      (∀ (φ : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ w φ).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ 1 ^ n)⁻¹ *
          ∫ y : FunctionsMetaplectic.Construction.Position ℝ n,
            φ.val y * ψ (-(∑ i, x i * y i)) ∂(FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ)) ∧
      (∀ g h : FunctionsMetaplectic.Construction.Metaplectic ℝ n ψ,
        FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ g = FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ h →
        ∃ ε : ℂ, ε ^ 2 = 1 ∧
          ∀ φ : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n,
            FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ h φ = ε • FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ g φ) := by
  obtain ⟨c, hc, rfl⟩ := RealCharacters.Construction.continuous_nontrivial_unitary_real_character ψ hContinuous hUnitary hNontrivial
  have ha := RealNormalization.Construction.real_analytic_normalization (Gaussian.Construction.realCharacter c) hContinuous hUnitary hNontrivial n
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2,
    RealFourierFamily.Construction.real_metaplecticProjection_surjective_parameter n c hc, ?_⟩
  obtain ⟨w, hw, hwa⟩ := RealWeyl.Construction.exists_real_weyl_metaplectic_parameter n c hc
  refine ⟨RealLevi.Construction.realLinearMetaplectic n hn (Gaussian.Construction.realCharacter c) hContinuous hUnitary hNontrivial,
    QuadraticIntertwiner.Construction.realQuadraticMetaplectic c, w, ?_, ?_, hw, ?_, ?_, hwa, ?_⟩
  · exact RealLevi.Construction.realLinearMetaplectic_projection n hn (Gaussian.Construction.realCharacter c) hContinuous hUnitary hNontrivial
  · exact QuadraticIntertwiner.Construction.realQuadraticMetaplectic_projection c
  · exact RealLevi.Construction.realLinearMetaplectic_apply n hn (Gaussian.Construction.realCharacter c) hContinuous hUnitary hNontrivial
  · exact QuadraticIntertwiner.Construction.realQuadraticMetaplectic_apply c
  · intro g h hgh
    exact real_metaplectic_same_projection_sign (Gaussian.Construction.realCharacter c) hContinuous hUnitary hNontrivial h g hgh.symm

end

end OAI.RepresentationTheory.Weil.Local.RealBareKernel.Construction
