import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak
import Mathlib.Analysis.Normed.Operator.Extend

/-! # Archimedean Space -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanSpace.Construction

noncomputable section

/-! The actual archimedean Bruhat space is dense in its reference L²
space. Linear norm identities on these test vectors determine pairings. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacters.LocalAnalysis _root_.MeasureTheory
open OAI.RepresentationTheory.Weil.UnitarySplitting.Weak.Construction (testToL2 referencePositionMeasure)
open scoped InnerProductSpace ENNReal

theorem archimedean_testToL2_dense
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (N : ℕ) :
    DenseRange (UnitarySplitting.Weak.Construction.testToL2 k N) := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := Local.FunctionsMetaplectic.Construction.Position k N) (F := ℂ) (p := (2 : ℝ≥0∞))
    (μ := UnitarySplitting.Weak.Construction.referencePositionMeasure k N) (by norm_num)
  apply hd.mono
  rintro _ ⟨φ, rfl⟩
  exact ⟨⟨φ, ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr ⟨φ, rfl⟩⟩, rfl⟩

theorem inner_eq_of_linear_norm_sq_eq
    {S V W : Type*} [AddCommGroup S] [Module ℂ S]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (L : S →ₗ[ℂ] V) (M : S →ₗ[ℂ] W) (h : ∀ f, ‖L f‖ ^ 2 = ‖M f‖ ^ 2) (f g : S) :
    ⟪L f, L g⟫_ℂ = ⟪M f, M g⟫_ℂ := by
  have hn (f : S) : ‖L f‖ = ‖M f‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h f)
  simp only [inner_eq_sum_norm_sq_div_four, ← map_add, ← map_sub, ← map_smul, hn]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanSpace.Construction
