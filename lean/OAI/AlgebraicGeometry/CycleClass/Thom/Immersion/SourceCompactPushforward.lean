import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.CompactStageNaturality

/-! # Source Compact Pushforward -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SourceCompactPushforward.Constructions.Construction

noncomputable section

/-! The global normalized Thom pushforward on actual compactly supported source cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceCompactThomPushforward (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) n ⟶
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) ((2 * p)+n) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomologyDesc (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) n
    (fun K => (SupportedThomSource.Constructions.Construction.regularSourceCompactThomStageIso Z a ha K n).hom ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) K) ((2 * p)+n))
    (by
      intro K L h
      rw [← Category.assoc, CompactStageNaturality.Constructions.Construction.regularSourceCompactThomStageIso_naturality,
        Category.assoc, AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyMap_ι])

theorem regularSourceCompactThomPushforward_stage (n : ℕ) (K : Compacts Z.regularAnalyticSpace) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) K n ≫
        regularSourceCompactThomPushforward Z a ha n =
      (SupportedThomSource.Constructions.Construction.regularSourceCompactThomStageIso Z a ha K n).hom ≫
        AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          (HodgeConjecture.DegreeTwo.OpenEmbeddingExtension.Constructions.embeddingCompactImage (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) K) ((2 * p)+n) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportCohomologyι_desc _ _ _ _ _ _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SourceCompactPushforward.Constructions.Construction
