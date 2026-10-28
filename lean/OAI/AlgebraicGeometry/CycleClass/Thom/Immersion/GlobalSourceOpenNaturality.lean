import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SourceOpenNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.SupportedThomSource

/-! # Global Source Open Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceOpenNaturality.Constructions.Construction

noncomputable section

/-! Restriction from the original global relative groups to an actual open neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_open_naturality
    (O U : Opens Z.regularAmbientSpace) (q : ℕ) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace)
      ((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj U) q ≫
        (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedRelativeIso Z a ha O U q).hom =
      (SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso Z a ha O q).hom ≫
        Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U ((2 * p)+q) := by
  have hn := SourceOpenNaturality.Constructions.Construction.regularSourceThomSupportedRelativeIso_open_naturality Z a ha O
    (homOfLE (le_top : U ≤ ⊤)) q
  rw [Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction_eq, Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction_eq]
  dsimp only [SupportedThomSource.Constructions.Construction.regularSourceThomSupportedGlobalIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun f =>
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (SourceSheaf.Constructions.Construction.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) q).inv ≫ f) hn

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.GlobalSourceOpenNaturality.Constructions.Construction
