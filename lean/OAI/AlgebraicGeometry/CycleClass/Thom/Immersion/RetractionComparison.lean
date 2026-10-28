import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Retraction
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.LocalSupportEquality

/-! # Retraction Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.RetractionComparison.Constructions

noncomputable section

/-! The local retraction formula is the restriction of the original
supported Thom isomorphism whenever the two actual source and target
supports agree on the neighborhood. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.LocalSupportEquality.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Retraction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.RetractionSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)
  (U : Opens V.analyticSpace)
  (r : TopCat.of U ⟶ TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
  (hr : HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U ≫ r = 𝟙 _)
  (O : Opens ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U))
  (W : Opens V.analyticSpace)
  (hW : HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen (X := V.analyticSpace) U (Retraction.Constructions.retractionOpen Z U r O) ≤ W)
  (es : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Z.regularAnalyticSpace)
    (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj W) : Set Z.regularAnalyticSpace)
      ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U) =
    (O : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)))
  (et : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace)
    ((Z.regularThomComplementOpen ⊔ W : Opens V.analyticSpace) : Set V.analyticSpace) U =
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := V.analyticSpace) (Z.regularThomComplementOpen : Set V.analyticSpace) U ∪
        (Retraction.Constructions.retractionOpen Z U r O : Set U))

include hW in
theorem retractionThomIso_eq_original (n : ℕ) :
    Retraction.Constructions.retractionThomIso Z a ha U r hr O n =
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr
      (TopCat.of ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) es n).symm ≪≫
      SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha W U n ≪≫
        AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of U) et (2 * p + n) := by
  let B := Retraction.Constructions.retractionOpen Z U r O
  have hs : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := Z.regularAnalyticSpace)
      (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj
        (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen (X := V.analyticSpace) U B)) : Set Z.regularAnalyticSpace)
      ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U) =
      (O : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)) :=
    (HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_source (X := V.analyticSpace) U B (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).trans
      (RetractionSupport.Constructions.source_preimage (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.openPreimageMap (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z) U) r hr
        (O : Set ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U)))
  have ht := HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.localSupportAmbientOpen_union (X := V.analyticSpace) U B Z.regularThomComplementOpen
  have hn := LocalSupportEquality.Constructions.Construction.regularSourceThomSupportedRelativeIso_supportEquality Z a ha hW U
    (es.trans hs.symm) (et.trans ht.symm) n
  unfold Retraction.Constructions.retractionThomIso LocalSupportCup.Constructions.Construction.regularSourceThomLocalSupportIso
  erw [hn]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr,
    eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.RetractionComparison.Constructions
