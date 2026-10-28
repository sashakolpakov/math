import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSourceNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.CompactStage

/-! # Compact Stage Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.CompactStageNaturality.Constructions.HigherThom

noncomputable section

/-! The actual compact source stages of the Thom isomorphism form a compatible directed system. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem relativeComplementChange_cast_naturality (X : TopCat.{0})
    {A B A' B' : Set X} (h : A ⊆ B) (h' : A' ⊆ B') (eA : A = A') (eB : B = B') (n : ℕ) :
    HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeComplementChange X h) n ≫
        (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) eA)).hom =
      (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X S n) eB)).hom ≫
        HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeComplementChange X h') n := by
  subst A'
  subst B'
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)

theorem regularCompactImageComplement_antitone {K L : Compacts Z.regularAnalyticSpace} (h : K ≤ L) :
    Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z L ≤ Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z K :=
  Set.compl_subset_compl.mpr (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage_mono (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) h)

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceCompactThomStageIso_naturality
    {K L : Compacts Z.regularAnalyticSpace} (h : K ≤ L) (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ) h n ≫ (Regular.CompactStage.Constructions.HigherThom.regularSourceCompactThomStageIso Z a ha L n).hom =
      (Regular.CompactStage.Constructions.HigherThom.regularSourceCompactThomStageIso Z a ha K n).hom ≫
        AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap (ModuleCat.of ℚ ℚ)
          (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage_mono (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) h) ((2 * p)+n) := by
  let hO := regularCompactImageComplement_antitone Z h
  exact Supported.SourceNaturality.Constructions.HigherThom.sourceTargetIso_naturality
    (eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAnalyticSpace) B n) (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement_preimage Z K)))
    (eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAnalyticSpace) B n) (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement_preimage Z L)))
    (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z K) n)
    (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z L) n)
    (eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) B ((2 * p)+n)) (Regular.CompactStage.Constructions.HigherThom.regularCompactThom_unionComplement Z K)))
    (eqToIso (congrArg (fun B => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) B ((2 * p)+n)) (Regular.CompactStage.Constructions.HigherThom.regularCompactThom_unionComplement Z L))) _ _ _ _
    (relativeComplementChange_cast_naturality (TopCat.of Z.regularAnalyticSpace)
      (show ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z L) :
        Set Z.regularAnalyticSpace) ⊆
        ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z K) :
          Set Z.regularAnalyticSpace) from fun _ hx => hO hx)
      (Set.compl_subset_compl.mpr h) (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement_preimage Z L)
      (Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement_preimage Z K) n)
    (GlobalSourceNaturality.Constructions.HigherThom.regularSourceThomSupportedGlobalIso_support_naturality Z a ha hO n)
    (relativeComplementChange_cast_naturality (TopCat.of Z.regularAmbientSpace)
      (show ((Z.regularThomComplementOpen ⊔ Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z L : Opens Z.regularAmbientSpace) :
        Set Z.regularAmbientSpace) ⊆
        ((Z.regularThomComplementOpen ⊔ Regular.CompactStage.Constructions.HigherThom.regularCompactImageComplement Z K : Opens Z.regularAmbientSpace) :
          Set Z.regularAmbientSpace) from sup_le_sup_left hO Z.regularThomComplementOpen)
      (Set.compl_subset_compl.mpr (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage_mono (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z) h))
      (Regular.CompactStage.Constructions.HigherThom.regularCompactThom_unionComplement Z L) (Regular.CompactStage.Constructions.HigherThom.regularCompactThom_unionComplement Z K) ((2 * p)+n))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.CompactStageNaturality.Constructions.HigherThom
