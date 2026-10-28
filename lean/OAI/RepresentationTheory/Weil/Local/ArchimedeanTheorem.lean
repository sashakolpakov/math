import OAI.RepresentationTheory.Weil.Local.RealFieldTheorem
import OAI.RepresentationTheory.Weil.Local.ComplexFieldTheorem

/-! # Archimedean Theorem -/

namespace OAI.RepresentationTheory.Weil.Local.ArchimedeanTheorem.Construction

noncomputable section

/-! Full repaired LocalWeil at every archimedean local field, with its actual chosen norm. -/

open _root_.MeasureTheory Filter
open scoped BigOperators _root_.Topology

theorem archimedean_schrodinger_generator_formulas
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (n : ℕ) (hn : 0 < n)
    (ψ : AddChar k ℂ)
    (hContinuous : Continuous (fun t : k => ψ t))
    (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hNontrivial : ∃ t : k, ψ t ≠ 1) :
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
  rcases ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, he, he'⟩ | ⟨e, he, he'⟩
  · exact RealFieldTheorem.Construction.realField_schrodinger_generator_formulas hNondiscrete hArch e he he' n hn ψ
      hContinuous hUnitary hNontrivial
  · exact ComplexFieldTheorem.Construction.complexField_schrodinger_generator_formulas hNondiscrete hArch e he he' n hn ψ
      hContinuous hUnitary hNontrivial

end

end OAI.RepresentationTheory.Weil.Local.ArchimedeanTheorem.Construction
