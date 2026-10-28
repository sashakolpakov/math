import OAI.AlgebraicGeometry.Comparison.Betti.TruncatedNaturality

/-! # Holomorphic Hodge Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.HolomorphicHodgeImage

noncomputable section

/-! The exact independent algebraic Hodge filtration maps to the independent holomorphic truncation image under the original projective comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem projectivePresentation_algebraicFiltration_map_holomorphic
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (n : ℕ) (r : ℤ) :
    (NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 X n r).map (Holomorphic.Hypercohomology.algebraicToHolomorphicCohomologyMap X n).hom =
      LinearMap.range (TruncatedNaturality.holomorphicTruncationClass X n r) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨z, rfl⟩ := (Algebraic.FiltrationExtension.filtration66_mem_iff_truncatedClass X n r a).mp ha
    exact ⟨Truncated.algebraicHolomorphicTruncatedCohomologyMap X r (n : ℤ) z,
      (TruncatedNaturality.algebraicHolomorphicTruncationClass_naturality X n r z).symm⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := (Truncated.projectivePresentation_truncatedComparison_bijective X P r (n : ℤ)).surjective b
    refine ⟨Algebraic.FiltrationExtension.algebraicTruncationClass X n r a,
      (Algebraic.FiltrationExtension.filtration66_mem_iff_truncatedClass X n r _).mpr ⟨a, rfl⟩, ?_⟩
    exact (TruncatedNaturality.algebraicHolomorphicTruncationClass_naturality X n r a).trans
      (congrArg (TruncatedNaturality.holomorphicTruncationClass X n r) ha)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.HolomorphicHodgeImage
