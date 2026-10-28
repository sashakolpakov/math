import OAI.RepresentationTheory.Weil.Local.ComplexBareKernel
import OAI.RepresentationTheory.Weil.Local.ComplexLevi

/-! # Complex Theorem -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexTheorem.Construction

noncomputable section

/-! All clauses of the repaired LocalWeil theorem at the complex place. -/

open _root_.MeasureTheory Filter
open scoped BigOperators _root_.Topology

theorem complex_schrodinger_generator_formulas
    (n : ℕ) (hn : 0 < n)
    (ψ : AddChar ℂ ℂ)
    (hContinuous : Continuous (fun t : ℂ => ψ t))
    (hUnitary : ∀ t : ℂ, ‖ψ t‖ = 1)
    (hNontrivial : ∃ t : ℂ, ψ t ≠ 1) :
    -- Positivity prevents the Haar normalization from degenerating.
    (0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ ψ) ∧
    (FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure ∧
    -- The Gaussian phase is taken from an actual nonzero oscillatory limit.
    (∀ a : ℂ, a ≠ 0 →
      Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian ℂ ψ a) (𝓝[>] (0 : ℝ))
        (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral ℂ ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral ℂ ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ a ^ 8 = 1) ∧
    -- The selected Haar measure is self-dual for the coordinate pairing.
    (∀ (φ : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n),
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) φ.val) x = φ.val (-x)) ∧
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ) ∧
    ∃ (m : FunctionsMetaplectic.Construction.GeneralLinear ℂ n → FunctionsMetaplectic.Construction.Metaplectic ℂ n ψ)
      (u : FunctionsMetaplectic.Construction.SymmetricMatrix ℂ n → FunctionsMetaplectic.Construction.Metaplectic ℂ n ψ)
      (w : FunctionsMetaplectic.Construction.Metaplectic ℂ n ψ),
      (∀ A : FunctionsMetaplectic.Construction.GeneralLinear ℂ n,
        FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ (m A) = Generators.Construction.leviSymplectic A) ∧
      (∀ B : FunctionsMetaplectic.Construction.SymmetricMatrix ℂ n,
        FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ (u B) = Generators.Construction.quadraticSymplectic B) ∧
      FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ w = Generators.Construction.weylSymplectic ℂ n ∧
      (∀ (A : FunctionsMetaplectic.Construction.GeneralLinear ℂ n) (φ : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ (m A) φ).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ (FunctionsMetaplectic.Construction.determinantUnit ℂ A) / FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1) *
          ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus ℂ (FunctionsMetaplectic.Construction.determinantUnit ℂ A)))⁻¹ : ℂ) *
          φ.val (Matrix.mulVec (↑(A⁻¹) : Matrix (Fin n) (Fin n) ℂ) x)) ∧
      (∀ (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℂ n) (φ : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ (u B) φ).val x =
          ψ ((∑ i, ∑ j, x i * B.val i j * x j) / 2) * φ.val x) ∧
      (∀ (φ : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ w φ).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n)⁻¹ *
          ∫ y : FunctionsMetaplectic.Construction.Position ℂ n,
            φ.val y * ψ (-(∑ i, x i * y i)) ∂(FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ)) ∧
      (∀ g h : FunctionsMetaplectic.Construction.Metaplectic ℂ n ψ,
        FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ g = FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ h →
        ∃ ε : ℂ, ε ^ 2 = 1 ∧
          ∀ φ : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n,
            FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ h φ = ε • FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ g φ) := by
  have ha := ComplexCover.Construction.complex_analytic_normalization ψ hContinuous hUnitary hNontrivial n
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2,
    ComplexCover.Construction.complex_metaplecticProjection_surjective n ψ hContinuous hUnitary hNontrivial, ?_⟩
  obtain ⟨w, hw, hwa⟩ := ComplexWeyl.Construction.exists_complex_weyl_metaplectic n ψ hContinuous hUnitary hNontrivial
  refine ⟨ComplexLevi.Construction.complexLinearMetaplectic n hn ψ hContinuous hUnitary hNontrivial,
    ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic ψ hContinuous hUnitary, w, ?_, ?_, hw, ?_, ?_, hwa, ?_⟩
  · exact ComplexLevi.Construction.complexLinearMetaplectic_projection n hn ψ hContinuous hUnitary hNontrivial
  · exact ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic_projection ψ hContinuous hUnitary
  · exact ComplexLevi.Construction.complexLinearMetaplectic_apply n hn ψ hContinuous hUnitary hNontrivial
  · exact ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic_apply ψ hContinuous hUnitary
  · intro g h hgh
    exact ComplexBareKernel.Construction.complex_metaplectic_same_projection_sign ψ hContinuous hUnitary hNontrivial h g hgh.symm

end

end OAI.RepresentationTheory.Weil.Local.ComplexTheorem.Construction
