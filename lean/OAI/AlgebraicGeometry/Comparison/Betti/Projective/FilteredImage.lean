import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.HolomorphicHodgeImage
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.HolomorphicFilteredImage

/-! # Filtered Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.FilteredImage.Integration

noncomputable section

/-! For an integral smooth projective variety, the original algebraic filtration has exactly the Betti classes represented by closed filtered smooth forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := V.property
local instance : Smooth V.toOver.hom := V.presentation.smooth
local instance : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V.toOver) := IntegrationDerivedClass.projectivePointIntegrationMetrizable V
local instance : StronglyLocallyContractibleSpace (TopCat.of V.analyticSpace) :=
  IntegrationDerivedClass.projectiveIntegrationLocallyContractible V

theorem projective_algebraicFiltration_image_iff (n : ℕ) (r : ℤ) (b : V.complexCohomology n) :
    (∃ a : Algebraic.Sheaves.algebraicDeRham V.toOver n,
      a ∈ NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 V.toOver n r ∧
      Betti.Smooth.ReferenceCongruence.bettiDownEquiv V.toOver n (Algebraic.Map.algebraicDeRhamBettiMap V.toOver n a) = b) ↔
    ∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n,
      a.val ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration V.analyticModel V.analyticSpace n r ∧
      (V.deRhamBettiIso n).hom (V.deRhamClass n a) = b := by
  have hf (a : Algebraic.Sheaves.algebraicDeRham V.toOver n) :
      (Holomorphic.DeRham.holomorphicBettiCohomologyIso V.toOver n).hom
        (Holomorphic.Hypercohomology.algebraicToHolomorphicCohomologyMap V.toOver n a) = Algebraic.Map.algebraicDeRhamBettiMap V.toOver n a :=
    congrArg (fun f => f a) (Holomorphic.DeRham.algebraicDeRhamBettiMap_holomorphic_factorization V.toOver n)
  have hm := HolomorphicHodgeImage.projectivePresentation_algebraicFiltration_map_holomorphic
    V.toOver V.presentation.projective n r
  have he : (∃ a : Algebraic.Sheaves.algebraicDeRham V.toOver n,
      a ∈ NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 V.toOver n r ∧
      Betti.Smooth.ReferenceCongruence.bettiDownEquiv V.toOver n (Algebraic.Map.algebraicDeRhamBettiMap V.toOver n a) = b) ↔
    ∃ c : TruncatedNaturality.holomorphicTruncatedCohomology V.toOver n r,
      Betti.Smooth.ReferenceCongruence.bettiDownEquiv V.toOver n ((Holomorphic.DeRham.holomorphicBettiCohomologyIso V.toOver n).hom
        (TruncatedNaturality.holomorphicTruncationClass V.toOver n r c)) = b := by
    constructor
    · rintro ⟨a, ha, hab⟩
      have hmem : Holomorphic.Hypercohomology.algebraicToHolomorphicCohomologyMap V.toOver n a ∈
          LinearMap.range (TruncatedNaturality.holomorphicTruncationClass V.toOver n r) :=
        hm ▸ ⟨a, ha, rfl⟩
      obtain ⟨c, hc⟩ := hmem
      exact ⟨c, (congrArg (fun z => Betti.Smooth.ReferenceCongruence.bettiDownEquiv V.toOver n
        ((Holomorphic.DeRham.holomorphicBettiCohomologyIso V.toOver n).hom z)) hc).trans
          ((congrArg (Betti.Smooth.ReferenceCongruence.bettiDownEquiv V.toOver n) (hf a)).trans hab)⟩
    · rintro ⟨c, hc⟩
      have hmem : TruncatedNaturality.holomorphicTruncationClass V.toOver n r c ∈
          (NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 V.toOver n r).map
            (Holomorphic.Hypercohomology.algebraicToHolomorphicCohomologyMap V.toOver n).hom :=
        hm.symm ▸ ⟨c, rfl⟩
      obtain ⟨a, ha, hac⟩ := hmem
      refine ⟨a, ha, ?_⟩
      exact (congrArg (Betti.Smooth.ReferenceCongruence.bettiDownEquiv V.toOver n) (hf a).symm).trans
        ((congrArg (fun z => Betti.Smooth.ReferenceCongruence.bettiDownEquiv V.toOver n
          ((Holomorphic.DeRham.holomorphicBettiCohomologyIso V.toOver n).hom z)) hac).trans hc)
  rw [he, Holomorphic.FilteredNormalization.holomorphicBettiCohomologyIso_truncation_image_iff]
  rw [← DerivedNormalization.Integration.projective_standardResolutionIso V]
  exact HolomorphicFilteredImage.Integration.projective_holomorphicTruncation_image_iff V n r b

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.FilteredImage.Integration
