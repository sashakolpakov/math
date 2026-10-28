import OAI.RepresentationTheory.Weil.Local.Generators
import OAI.RepresentationTheory.Weil.Local.Gaussian
import OAI.RepresentationTheory.Weil.Local.RealFourierLp
import OAI.RepresentationTheory.Weil.Local.RealNormalization
import OAI.RepresentationTheory.Weil.Local.ArchimedeanTestSpace
import OAI.RepresentationTheory.Weil.Local.RealCover
import OAI.RepresentationTheory.Weil.Local.RealFourierFamily
import OAI.RepresentationTheory.Weil.Local.CompactCharacter
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanCover
import OAI.RepresentationTheory.Weil.Local.AnnihilatorDuality
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanHaar
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanNormalization
import OAI.RepresentationTheory.Weil.Local.GaussianCompact
import OAI.RepresentationTheory.Weil.Local.FiniteQuadraticPhase
import OAI.RepresentationTheory.Weil.Local.GaussianNonarchimedean
import OAI.RepresentationTheory.Weil.Local.NormalizedFresnel
import OAI.RepresentationTheory.Weil.Local.BruhatCosets
import OAI.RepresentationTheory.Weil.Local.BareGeneration
import OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses
import OAI.RepresentationTheory.Weil.Local.ComplexCover
import OAI.RepresentationTheory.Weil.Local.ComplexLevi
import OAI.RepresentationTheory.Weil.Local.RealWeyl
import OAI.RepresentationTheory.Weil.Local.ComplexWeyl
import OAI.RepresentationTheory.Weil.Local.GeneralSchur
import OAI.RepresentationTheory.Weil.Local.ComplexTheorem
import OAI.RepresentationTheory.Weil.Local.SquareDeterminantLift
import OAI.RepresentationTheory.Weil.Local.RealLevi
import OAI.RepresentationTheory.Weil.Local.SiegelGaussian
import OAI.RepresentationTheory.Weil.Local.RealOscillator
import OAI.RepresentationTheory.Weil.Local.RealStandardBareKernel
import OAI.RepresentationTheory.Weil.Local.RealBareKernel
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanLevi
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanSquareMinusOne
import OAI.RepresentationTheory.Weil.Local.ArchimedeanKernel
import OAI.RepresentationTheory.Weil.Local.ComplexTransportedNorm
import OAI.RepresentationTheory.Weil.Local.RealPower
import OAI.RepresentationTheory.Weil.Local.RealFieldAnalytic
import OAI.RepresentationTheory.Weil.Local.RealFieldTheorem
import OAI.RepresentationTheory.Weil.Local.PlanarRadialTransfer
import OAI.RepresentationTheory.Weil.Local.PlanarPowerDamping
import OAI.RepresentationTheory.Weil.Local.RadialTailCutoffBound
import OAI.RepresentationTheory.Weil.Local.PlanarIntegral
import OAI.RepresentationTheory.Weil.Local.ComplexPowerGaussian
import OAI.RepresentationTheory.Weil.Local.ArchimedeanTheorem
import OAI.RepresentationTheory.Weil.Local.Analytic
import OAI.RepresentationTheory.Weil.Local.LocalGenerators
import OAI.RepresentationTheory.Weil.Local.CompactGroupIndex
import OAI.RepresentationTheory.Weil.Local.PrincipalSquareClasses
import OAI.RepresentationTheory.Weil.Local.NormSmallSubgroup
import OAI.RepresentationTheory.Weil.Local.FiniteSquareClasses
import OAI.RepresentationTheory.Weil.Local.QuadraticNormIndex
import OAI.RepresentationTheory.Weil.Local.GaussianSquareCharacter
import OAI.RepresentationTheory.Weil.Local.CharacterExtension
import OAI.RepresentationTheory.Weil.Local.FourierNormalForm
import OAI.RepresentationTheory.Weil.Local.GeneralGaussianCoefficient
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanBareKernel
import Lean.Util.CollectAxioms

/-! # Formulas -/

namespace OAI.RepresentationTheory.Weil.Local.Formulas

noncomputable section

/-!
LocalWeil construction entry point and exhaustive helper axiom audit.
The admitted target in Statements/LocalWeil.lean is deliberately not imported.
Every declaration, including generated declarations, in the LocalWeil
construction and proof modules is checked against the standard classical foundations.
The full repaired local-field theorem is proved below, with the statement file unchanged.

The analytic normalization and prescribed bare generators are assembled by
`localField_analytic_normalization` and `localField_metaplectic_generators`.
The archimedean kernel follows from the real and complex constructions and
transport along the classified topological field isomorphisms.

For a nonarchimedean field in which -1 is nonsquare, the normalized squared
Gaussian index is proved to be a quadratic character using the index-two
quadratic norm subgroup. General Fresnel pairing then gives a multiplicative
value on the oscillator Fourier cell. Extending that value to the whole
oscillator group produces a character whose value on a scalar operator z is
z². It kills commutators and the negative identity, so the intrinsically
defined bare metaplectic kernel consists of signs. The case in which -1 is
a square uses the checked conjugate-linear quarter-turn structure.
-/

open _root_.MeasureTheory Filter
open scoped BigOperators _root_.Topology

/-- The full repaired LocalWeil theorem, proved independently of the admitted statement module. -/
theorem schrodinger_generator_formulas
    (k : Type) [NormedField k] [CompleteSpace k]
    [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
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
  have ha := Analytic.Construction.localField_analytic_normalization hNondiscrete ψ hContinuous hUnitary hNontrivial n
  obtain ⟨hsurj, m, u, w, hm, hu, hw, hma, hua, hwa⟩ :=
    LocalGenerators.Construction.localField_metaplectic_generators hNondiscrete n hn ψ hContinuous hUnitary hNontrivial
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, hsurj, m, u, w, hm, hu, hw, hma, hua, hwa, ?_⟩
  intro g h hgh
  by_cases hArch : ∀ m : ℕ, ‖(m : k)‖ ≤ 1
  · let : IsUltrametricDist k :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    exact NonarchimedeanBareKernel.Construction.nonarchimedean_metaplectic_same_projection_sign hNondiscrete ψ hUnitary hContinuous
      hNontrivial h g hgh.symm
  · have hfull := ArchimedeanTheorem.Construction.archimedean_schrodinger_generator_formulas hNondiscrete hArch n hn ψ
      hContinuous hUnitary hNontrivial
    obtain ⟨_, _, _, _, _, _, _, _, _, hsign⟩ := hfull.2.2.2.2.2
    exact hsign g h hgh

end

end OAI.RepresentationTheory.Weil.Local.Formulas
