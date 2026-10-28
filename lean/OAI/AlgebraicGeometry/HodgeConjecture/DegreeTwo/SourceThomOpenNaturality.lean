import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomOpen
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom

/-! # Source Thom Open Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomOpenNaturality.Constructions

noncomputable section

/-! Restriction from the original global relative groups to an actual open neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_open_naturality
    (O U : Opens Z.regularAmbientSpace) (q : ℕ) :
    CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace)
      ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U) q ≫
        (SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso Z a ha O U q).hom =
      (GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso Z a ha O q).hom ≫
        CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          ((Z.regularThomComplementOpen ⊔ O : Opens Z.regularAmbientSpace) : Set Z.regularAmbientSpace) U (2+q) := by
  have hn := SourceThomOpen.Constructions.regularSourceThomSupportedRelativeIso_open_naturality Z a ha O
    (homOfLE (le_top : U ≤ ⊤)) q
  rw [CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction_eq, CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction_eq]
  dsimp only [GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congrArg (fun f =>
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace)
      (((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj O : Opens Z.regularAnalyticSpace) : Set Z.regularAnalyticSpace) q).inv ≫ f) hn

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SourceThomOpenNaturality.Constructions
