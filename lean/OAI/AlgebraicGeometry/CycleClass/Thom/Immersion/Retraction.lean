import OAI.AlgebraicGeometry.CycleClass.Thom.RetractionSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.LocalSupportCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalRetractionSplit

/-! # Retraction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Retraction.Constructions

noncomputable section

/-! The actual supported Thom isomorphism on an open with a genuine
source retraction is cup with the restricted Thom class and retraction
pullback. The support may be any closed source subset. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.LocalSupportCup.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.RetractionSupport.Constructions OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalRetractionSplit.Constructions

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)
  (U : Opens V.analyticSpace)
  (r : TopCat.of U ⟶ TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
  (hr : HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U ≫ r = 𝟙 _)
  (O : Opens ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))

def retractionOpen : Opens U :=
  ⟨r ⁻¹' (O : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)),
    O.isOpen.preimage r.hom.continuous⟩

def retractionThomIso (q : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
      (O : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) q ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
        (Z.regularThomComplementOpen : Set V.analyticSpace) U ∪
        (retractionOpen Z U r O : Set U)) (2 * p + q) :=
  (eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) S q)
      (RetractionSupport.Constructions.source_preimage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U) r hr
        (O : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))))).symm ≪≫
    LocalSupportCup.Constructions.Construction.regularSourceThomLocalSupportIso Z a ha U (retractionOpen Z U r O) q

theorem retractionThomIso_eq_cup (q : ℕ) :
    (retractionThomIso Z a ha U r hr O q).hom =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) r
      (A := (retractionOpen Z U r O : Set U))
      (B := (O : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)))
      (fun _ hx => hx) q ≫
    ModuleCat.ofHom (HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of U)
      (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
        (Z.regularThomComplementOpen : Set V.analyticSpace) U)
      (retractionOpen Z U r O : Set U)
      (Z.regularThomComplementOpen.isOpen.preimage continuous_subtype_val)
      (retractionOpen Z U r O).isOpen (2 * p) q
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) V.analyticSpace
        (Z.regularThomComplementOpen : Set V.analyticSpace) U (2 * p) Z.regularThomClass)) := by
  let s := eqToIso (congrArg (fun S => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) S q)
      (RetractionSupport.Constructions.source_preimage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U) r hr
        (O : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))))
  have hs := RetractionSupport.Constructions.relativePullback_split_raw (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U)
    r hr (O : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) q
  have hc := LocalSupportCup.Constructions.Construction.regularSourceThomLocalSupportIso_cup Z a ha U (retractionOpen Z U r O) q
  have he := HodgeConjecture.DegreeTwo.NormalRetractionSplit.Constructions.splitSourceIso_cup _ _ s (LocalSupportCup.Constructions.Construction.regularSourceThomLocalSupportIso Z a ha U
    (retractionOpen Z U r O) q) (Iso.refl _) _ hs hc
  simpa only [retractionThomIso, s, Iso.trans_hom, Iso.refl_hom, Category.comp_id] using he

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Retraction.Constructions
