import OAI.RepresentationTheory.Weil.Local.QuarterTurnKernel
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanLevi

/-! # Nonarchimedean Square Minus One -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanSquareMinusOne.Construction

noncomputable section

/-! All repaired LocalWeil clauses at nonarchimedean places where -1 is a square. -/

open _root_.MeasureTheory Filter
open scoped BigOperators _root_.Topology

theorem nonarchimedean_schrodinger_generator_formulas_of_sqrt_neg_one
    (k : Type) [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (n : ℕ) (hn : 0 < n)
    (ψ : AddChar k ℂ)
    (hContinuous : Continuous (fun t : k => ψ t))
    (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hNontrivial : ∃ t : k, ψ t ≠ 1)
    (r : k) (hr : r ^ 2 = -1) :
    -- Positivity prevents the Haar normalization from degenerating.
    (0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) ∧
    (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure ∧
    -- The Gaussian phase is taken from an actual nonzero oscillatory limit.
    (∀ a : k, a ≠ 0 →
      Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ))
        (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex k ψ a ^ 8 = 1) ∧
    -- The selected Haar measure is self-dual for the coordinate pairing.
    (∀ (φ : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) φ.val) x = φ.val (-x)) ∧
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection k n ψ) ∧
    ∃ (m : FunctionsMetaplectic.Construction.GeneralLinear k n → FunctionsMetaplectic.Construction.Metaplectic k n ψ)
      (u : FunctionsMetaplectic.Construction.SymmetricMatrix k n → FunctionsMetaplectic.Construction.Metaplectic k n ψ)
      (w : FunctionsMetaplectic.Construction.Metaplectic k n ψ),
      (∀ A : FunctionsMetaplectic.Construction.GeneralLinear k n,
        FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (m A) = Generators.Construction.leviSymplectic A) ∧
      (∀ B : FunctionsMetaplectic.Construction.SymmetricMatrix k n,
        FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (u B) = Generators.Construction.quadraticSymplectic B) ∧
      FunctionsMetaplectic.Construction.metaplecticProjection k n ψ w = Generators.Construction.weylSymplectic k n ∧
      (∀ (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (φ : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
        (FunctionsMetaplectic.Construction.weilRepresentation k n ψ (m A) φ).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex k ψ (FunctionsMetaplectic.Construction.determinantUnit k A) / FunctionsMetaplectic.Construction.gaussianIndex k ψ 1) *
          ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)))⁻¹ : ℂ) *
          φ.val (Matrix.mulVec (↑(A⁻¹) : Matrix (Fin n) (Fin n) k) x)) ∧
      (∀ (B : FunctionsMetaplectic.Construction.SymmetricMatrix k n) (φ : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
        (FunctionsMetaplectic.Construction.weilRepresentation k n ψ (u B) φ).val x =
          ψ ((∑ i, ∑ j, x i * B.val i j * x j) / 2) * φ.val x) ∧
      (∀ (φ : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
        (FunctionsMetaplectic.Construction.weilRepresentation k n ψ w φ).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n)⁻¹ *
          ∫ y : FunctionsMetaplectic.Construction.Position k n,
            φ.val y * ψ (-(∑ i, x i * y i)) ∂(FunctionsMetaplectic.Construction.positionMeasure k n ψ)) ∧
      (∀ g h : FunctionsMetaplectic.Construction.Metaplectic k n ψ,
        FunctionsMetaplectic.Construction.metaplecticProjection k n ψ g = FunctionsMetaplectic.Construction.metaplecticProjection k n ψ h →
        ∃ ε : ℂ, ε ^ 2 = 1 ∧
          ∀ φ : FunctionsMetaplectic.Construction.schwartzBruhat k n,
            FunctionsMetaplectic.Construction.weilRepresentation k n ψ h φ = ε • FunctionsMetaplectic.Construction.weilRepresentation k n ψ g φ) := by
  have ha := GaussianNonarchimedean.Construction.nonarchimedean_analytic_normalization hNondiscrete ψ hUnitary hContinuous hNontrivial n
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2,
    NonarchimedeanCover.Construction.nonarchimedean_metaplecticProjection_surjective hNondiscrete n ψ hUnitary hContinuous hNontrivial, ?_⟩
  obtain ⟨w, hw, hwa⟩ := NormalizedFresnel.Construction.exists_nonarchimedean_weyl_metaplectic hNondiscrete n ψ hUnitary hContinuous hNontrivial
  refine ⟨NonarchimedeanLevi.Construction.nonarchimedeanLinearMetaplectic hNondiscrete n hn ψ hUnitary hContinuous hNontrivial,
    NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hUnitary hContinuous, w, ?_, ?_, hw, ?_, ?_, hwa, ?_⟩
  · exact NonarchimedeanLevi.Construction.nonarchimedeanLinearMetaplectic_projection hNondiscrete n hn ψ hUnitary hContinuous hNontrivial
  · exact NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic_projection hNondiscrete ψ hUnitary hContinuous
  · exact NonarchimedeanLevi.Construction.nonarchimedeanLinearMetaplectic_apply hNondiscrete n hn ψ hUnitary hContinuous hNontrivial
  · exact NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic_apply hNondiscrete ψ hUnitary hContinuous
  · intro g h hgh
    exact QuarterTurnKernel.Construction.nonarchimedean_metaplectic_same_projection_sign_of_sqrt_neg_one hNondiscrete ψ hUnitary hContinuous
      hNontrivial r hr h g hgh.symm

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanSquareMinusOne.Construction
