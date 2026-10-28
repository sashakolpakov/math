import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.SupportCup
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.SourceNaturality

/-! # Support Equality -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.SupportEquality

noncomputable section

/-! Equal actual source and Thom supports on an open neighborhood give the same native supported Thom isomorphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.HigherThom

theorem relativeComplementChange_eq_congr (X : TopCat.{0}) {A B : Set X}
    (h : A ⊆ B) (e : B = A) (n : ℕ) :
    HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeComplementChange X h) n =
      (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X e n).hom := by
  subst B
  change AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X h n = 𝟙 _
  exact AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap_refl X A n

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = D.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_supportEquality
    {O P : Opens D.regularAmbientSpace} (h : O ≤ P) (U : Opens D.regularAmbientSpace)
    (es : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace)
      (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V D)).obj P) : Set D.regularAnalyticSpace)
      ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V D)).obj U) =
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace)
      (((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V D)).obj O) : Set D.regularAnalyticSpace)
      ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V D)).obj U))
    (et : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      ((D.regularThomComplementOpen ⊔ P : Opens D.regularAmbientSpace) : Set D.regularAmbientSpace) U =
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      ((D.regularThomComplementOpen ⊔ O : Opens D.regularAmbientSpace) : Set D.regularAmbientSpace) U) (n : ℕ) :
    Supported.SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso D a ha O U n =
      (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V D)).obj U)) es n).symm ≪≫
      Supported.SourceIso.Constructions.HigherThom.regularSourceThomSupportedRelativeIso D a ha P U n ≪≫
      AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of U) et ((2 * p)+n) := by
  have hn := Supported.SourceNaturality.Constructions.HigherThom.regularSourceThomSupportedRelativeIso_support_naturality D a ha h U n
  have hs := relativeComplementChange_eq_congr
    (TopCat.of ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V D)).obj U)) (fun _ hx => h hx) es n
  have ht := relativeComplementChange_eq_congr (TopCat.of U)
    (fun _ hx => (sup_le_sup_left h D.regularThomComplementOpen) hx) et ((2 * p)+n)
  change HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSourceRelativeSupportChange (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V D) h U) n = _ at hs
  change HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.IntersectSupportNaturality.Constructions.relativeOpenComplementChange
    (X := TopCat.of D.regularAmbientSpace) (sup_le_sup_left h D.regularThomComplementOpen) U) ((2 * p)+n) = _ at ht
  rw [hs, ht] at hn
  apply Iso.ext
  apply (cancel_epi (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr
    (TopCat.of ((Opens.map (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V D)).obj U)) es n).hom).1
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, Category.assoc] using hn

end Constructions.HigherThom

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.SupportEquality
