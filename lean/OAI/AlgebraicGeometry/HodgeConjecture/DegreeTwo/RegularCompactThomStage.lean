import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom

/-! # Regular Compact Thom Stage -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions

noncomputable section

/-! The global Thom isomorphism at an exact compact source support and its actual ambient image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

def regularCompactImageComplement (K : Compacts Z.regularAnalyticSpace) : Opens Z.regularAmbientSpace :=
  ⟨(OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) K : Set Z.regularAmbientSpace)ᶜ,
    (OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) K).isCompact.isClosed.isOpen_compl⟩

theorem regularCompactImageComplement_preimage (K : Compacts Z.regularAnalyticSpace) :
    (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj (regularCompactImageComplement Z K) :
      Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) = (K : Set Z.regularAnalyticSpace)ᶜ := by
  change (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) ⁻¹'
    ((RegularTopGysin.Constructions.regularSourceInclusionMap V Z) '' (K : Set Z.regularAnalyticSpace))ᶜ = _
  have hf : Function.Injective (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) :=
    Z.isClosedEmbedding_regularComplementInclusion.injective
  rw [Set.preimage_compl, Set.preimage_image_eq _ hf]

theorem regularThomComplement_le_compactComplement (K : Compacts Z.regularAnalyticSpace) :
    Z.regularThomComplementOpen ≤ regularCompactImageComplement Z K := by
  intro y hy
  change y ∉ Set.range Z.regularComplementInclusion at hy
  change y ∉ (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) '' (K : Set Z.regularAnalyticSpace)
  rintro ⟨x, hx, hxy⟩
  exact hy ⟨x, hxy⟩

theorem regularCompactThom_unionComplement (K : Compacts Z.regularAnalyticSpace) :
    ((Z.regularThomComplementOpen ⊔ regularCompactImageComplement Z K : Opens Z.regularAmbientSpace) :
      Set Z.regularAmbientSpace) =
    (OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) K : Set Z.regularAmbientSpace)ᶜ := by
  rw [sup_eq_right.mpr (regularThomComplement_le_compactComplement Z K)]
  rfl

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceCompactThomStageIso (K : Compacts Z.regularAnalyticSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (K : Set Z.regularAnalyticSpace)ᶜ n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      (OpenEmbeddingExtension.Constructions.embeddingCompactImage (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) K : Set Z.regularAmbientSpace)ᶜ (2+n) :=
  (eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of Z.regularAnalyticSpace) B n) (regularCompactImageComplement_preimage Z K))).symm ≪≫
    GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha (regularCompactImageComplement Z K) n ≪≫
    eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) B (2+n)) (regularCompactThom_unionComplement Z K))

theorem regularSourceCompactThomStageIso_eq
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
    (hb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b = Z.regularThomClass) (K : Compacts Z.regularAnalyticSpace) (n : ℕ) :
    regularSourceCompactThomStageIso Z a ha K n = regularSourceCompactThomStageIso Z b hb K n := by
  unfold regularSourceCompactThomStageIso
  rw [GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso_eq Z a ha b hb]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions
