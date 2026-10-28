import OAI.AlgebraicGeometry.CycleClass.Thom.SourceOpenNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSupportedSource

/-! # Global Source Open Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSourceOpenNaturality.Constructions.HigherThom

noncomputable section

/-! Restriction from the original global relative groups to an actual open neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_open_naturality
    (O U : Opens Z.regularAmbientSpace) (q : ℕ) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace)
      ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj U) q ≫
        (Supported.SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso Z a ha O U q).hom =
      (GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso Z a ha O q).hom ≫
        Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U ((2 * p)+q) := by
  have hn := SourceOpenNaturality.Constructions.HigherThom.regularSourceThomSupportedRelativeIso_open_naturality Z a ha O
    (homOfLE (le_top : U ≤ ⊤)) q
  rw [Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction_eq, Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction_eq]
  dsimp only [GlobalSupportedSource.Constructions.HigherThom.regularSourceThomSupportedGlobalIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun f =>
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) q).inv ≫ f) hn

end

end OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSourceOpenNaturality.Constructions.HigherThom
