import OAI.RepresentationTheory.Weil.Local.ArchimedeanTheorem
import OAI.RepresentationTheory.Weil.Local.NonarchimedeanLevi
import Mathlib.Analysis.Normed.Field.Ultra

/-! # Local Generators -/

namespace OAI.RepresentationTheory.Weil.Local.LocalGenerators.Construction

noncomputable section

/-! Exact prescribed bare metaplectic generators over every field in the LocalWeil hypotheses.
This helper does not assert the remaining general nonarchimedean kernel-sign clause. -/

open _root_.MeasureTheory
open scoped BigOperators

theorem localField_metaplectic_generators
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (n : ℕ) (hn : 0 < n)
    (ψ : AddChar k ℂ)
    (hContinuous : Continuous (fun t : k => ψ t))
    (hUnitary : ∀ t : k, ‖ψ t‖ = 1)
    (hNontrivial : ∃ t : k, ψ t ≠ 1) :
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
            φ.val y * ψ (-(∑ i, x i * y i)) ∂(FunctionsMetaplectic.Construction.positionMeasure k n ψ)) := by
  by_cases hArch : ∀ m : ℕ, ‖(m : k)‖ ≤ 1
  · let : IsUltrametricDist k :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    refine ⟨NonarchimedeanCover.Construction.nonarchimedean_metaplecticProjection_surjective hNondiscrete n ψ
      hUnitary hContinuous hNontrivial, ?_⟩
    obtain ⟨w, hw, hwa⟩ := NormalizedFresnel.Construction.exists_nonarchimedean_weyl_metaplectic hNondiscrete n ψ
      hUnitary hContinuous hNontrivial
    refine ⟨NonarchimedeanLevi.Construction.nonarchimedeanLinearMetaplectic hNondiscrete n hn ψ hUnitary hContinuous hNontrivial,
      NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hUnitary hContinuous, w,
      NonarchimedeanLevi.Construction.nonarchimedeanLinearMetaplectic_projection hNondiscrete n hn ψ hUnitary hContinuous hNontrivial,
      NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic_projection hNondiscrete ψ hUnitary hContinuous,
      hw, NonarchimedeanLevi.Construction.nonarchimedeanLinearMetaplectic_apply hNondiscrete n hn ψ hUnitary hContinuous hNontrivial,
      NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic_apply hNondiscrete ψ hUnitary hContinuous, hwa⟩
  · have h := ArchimedeanTheorem.Construction.archimedean_schrodinger_generator_formulas hNondiscrete hArch n hn ψ
      hContinuous hUnitary hNontrivial
    obtain ⟨m, u, w, hm, hu, hw, hma, hua, hwa, _⟩ := h.2.2.2.2.2
    exact ⟨h.2.2.2.2.1, m, u, w, hm, hu, hw, hma, hua, hwa⟩

end

end OAI.RepresentationTheory.Weil.Local.LocalGenerators.Construction
