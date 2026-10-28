import OAI.RepresentationTheory.Weil.Local.ComplexTheorem
import OAI.RepresentationTheory.Weil.Local.ComplexFieldAnalytic
import OAI.RepresentationTheory.Weil.Local.FieldOscillator
import OAI.RepresentationTheory.Weil.Local.FieldCoordinates
import OAI.RepresentationTheory.Weil.Local.FieldGeneratorMatrices
import OAI.RepresentationTheory.Weil.Local.ArchimedeanKernel

/-! # Complex Field Theorem -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFieldTheorem.Construction

noncomputable section

/-! All clauses of repaired LocalWeil for every complex topological field presentation. -/

open _root_.MeasureTheory Filter
open scoped BigOperators _root_.Topology

theorem complexField_schrodinger_generator_formulas
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
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
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let η := FieldFourier.Construction.fieldCharacter e ψ
  have hηc := ArchimedeanKernel.Construction.fieldCharacter_continuous e he' ψ hContinuous
  have hηu := ArchimedeanKernel.Construction.fieldCharacter_unitary e ψ hUnitary
  have hηn := ArchimedeanKernel.Construction.fieldCharacter_nontrivial e ψ hNontrivial
  have ha := ComplexFieldAnalytic.Construction.complexField_analytic_normalization hNondiscrete hArch e he he' ψ
    hContinuous hUnitary hNontrivial n
  obtain ⟨_, hηHaar, _, _, hsurj, m, u, w, hm, hu, hw, hma, hua, hwa, _⟩ :=
    ComplexTheorem.Construction.complex_schrodinger_generator_formulas n hn η hηc hηu hηn
  let : (FunctionsMetaplectic.Construction.selfDualMeasure ℂ η).IsAddHaarMeasure := hηHaar
  have hγ (a : k) (ha : a ≠ 0) : FunctionsMetaplectic.Construction.gaussianIndex k ψ a = FunctionsMetaplectic.Construction.gaussianIndex ℂ η (e a) :=
    by
      rw [(ComplexFieldGaussian.Construction.complexField_gaussian_normalization hArch e he he' ψ hContinuous hUnitary hNontrivial a ha).2.2,
        (ArchimedeanTestSpace.Construction.complex_gaussian_normalization η hηc hηu hηn (e a) ((map_ne_zero e).mpr ha)).2.2]
  have hγ1 : FunctionsMetaplectic.Construction.gaussianIndex ℂ η 1 = FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 := by
    simpa only [map_one] using (hγ 1 one_ne_zero).symm
  refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2,
    FieldOscillator.Construction.field_metaplecticProjection_surjective e he he' n ψ hsurj,
    (fun A => FieldOscillator.Construction.fieldMetaplecticPullback e he he' n ψ (m (FieldGeneratorMatrices.Construction.fieldGeneralLinear e n A))),
    (fun B => FieldOscillator.Construction.fieldMetaplecticPullback e he he' n ψ (u (FieldGeneratorMatrices.Construction.fieldSymmetricMatrix e B))),
    FieldOscillator.Construction.fieldMetaplecticPullback e he he' n ψ w, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    rw [FieldOscillator.Construction.fieldMetaplecticPullback_projection, hm, ← FieldGeneratorMatrices.Construction.fieldSymplecticMap_levi, FieldOscillator.Construction.fieldSymplecticMap_symm]
  · intro B
    rw [FieldOscillator.Construction.fieldMetaplecticPullback_projection, hu, ← FieldGeneratorMatrices.Construction.fieldSymplecticMap_quadratic, FieldOscillator.Construction.fieldSymplecticMap_symm]
  · rw [FieldOscillator.Construction.fieldMetaplecticPullback_projection, hw, ← FieldGeneratorMatrices.Construction.fieldSymplecticMap_weyl e n, FieldOscillator.Construction.fieldSymplecticMap_symm]
  · intro A f x
    have hγdet : FunctionsMetaplectic.Construction.gaussianIndex ℂ η (FunctionsMetaplectic.Construction.determinantUnit ℂ (FieldGeneratorMatrices.Construction.fieldGeneralLinear e n A)) =
        FunctionsMetaplectic.Construction.gaussianIndex k ψ (FunctionsMetaplectic.Construction.determinantUnit k A) := by
      rw [FieldGeneratorMatrices.Construction.fieldGeneralLinear_determinant]
      exact (hγ (FunctionsMetaplectic.Construction.determinantUnit k A) (FunctionsMetaplectic.Construction.determinantUnit k A).ne_zero).symm
    have hmod : FunctionsMetaplectic.Construction.localModulus ℂ (FunctionsMetaplectic.Construction.determinantUnit ℂ (FieldGeneratorMatrices.Construction.fieldGeneralLinear e n A)) =
        FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) := by
      rw [FieldGeneratorMatrices.Construction.fieldGeneralLinear_determinant]
      exact (FieldCoordinates.Construction.field_localModulus e he he' (FunctionsMetaplectic.Construction.determinantUnit k A)).symm
    rw [FieldOscillator.Construction.fieldMetaplecticPullback_apply, hma, hγdet, hγ1, hmod]
    change _ * f.val (fun i => e.symm (Matrix.mulVec
      (↑((FieldGeneratorMatrices.Construction.fieldGeneralLinear e n A)⁻¹) : Matrix (Fin n) (Fin n) ℂ) (fun j => e (x j)) i)) = _
    rw [FieldGeneratorMatrices.Construction.fieldGeneralLinear_inverse_mulVec]
  · intro B f x
    rw [FieldOscillator.Construction.fieldMetaplecticPullback_apply, hua]
    change ψ (e.symm ((∑ i, ∑ j, e (x i) * (FieldGeneratorMatrices.Construction.fieldSymmetricMatrix e B).val i j * e (x j)) / 2)) *
      f.val (fun i => e.symm (e (x i))) = _
    rw [FieldGeneratorMatrices.Construction.fieldSymmetricMatrix_quadratic]
    simp only [RingEquiv.symm_apply_apply]
  · intro f x
    rw [FieldOscillator.Construction.fieldMetaplecticPullback_apply, hwa, hγ1]
    have hmap := (ComplexFieldNormalization.Construction.complexField_selfDual_normalization e he he' ψ hContinuous hUnitary hNontrivial).2.2
    have hF := FieldFourier.Construction.field_fourierIntegral e he he' (FunctionsMetaplectic.Construction.selfDualMeasure k ψ) (FunctionsMetaplectic.Construction.selfDualMeasure ℂ η)
      hmap n ψ f.val (fun i => e (x i))
    simp only [RingEquiv.symm_apply_apply] at hF
    exact congrArg (fun z : ℂ => (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ n)⁻¹ * z) hF
  · intro g h hgh
    have hker : FunctionsMetaplectic.Construction.metaplecticProjection k n ψ (h * g⁻¹) = 1 := by
      rw [map_mul, map_inv, hgh, mul_inv_cancel]
    obtain ⟨ε, hε, hs⟩ := ArchimedeanKernel.Construction.archimedean_metaplectic_kernel_sign hNondiscrete hArch ψ
      hContinuous hUnitary hNontrivial (h * g⁻¹) hker
    refine ⟨ε, hε, fun f => ?_⟩
    have hh := hs (g.val.val.2 f)
    change h.val.val.2 (g.val.val.2.symm (g.val.val.2 f)) = ε • g.val.val.2 f at hh
    simpa only [LinearEquiv.symm_apply_apply] using! hh

end

end OAI.RepresentationTheory.Weil.Local.ComplexFieldTheorem.Construction
