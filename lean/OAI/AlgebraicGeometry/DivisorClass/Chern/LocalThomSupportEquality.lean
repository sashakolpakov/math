import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ThomSupportEquality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportCup

/-! # Local Thom Support Equality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LocalThomSupportEquality

noncomputable section

/-! Equal actual source and Thom supports on an open neighborhood give the same native supported Thom isomorphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalSupportCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_supportEquality
    {O P : Opens D.regularAmbientSpace} (h : O ≤ P) (U : Opens D.regularAmbientSpace)
    (es : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace)
      (((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj P) : Set D.regularAnalyticSpace)
      ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U) =
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAnalyticSpace)
      (((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj O) : Set D.regularAnalyticSpace)
      ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U))
    (et : AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      ((D.regularThomComplementOpen ⊔ P : Opens D.regularAmbientSpace) : Set D.regularAmbientSpace) U =
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of D.regularAmbientSpace)
      ((D.regularThomComplementOpen ⊔ O : Opens D.regularAmbientSpace) : Set D.regularAmbientSpace) U) (n : ℕ) :
    HodgeConjecture.DegreeTwo.SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso D a ha O U n =
      (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U)) es n).symm ≪≫
      HodgeConjecture.DegreeTwo.SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso D a ha P U n ≪≫
      AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of U) et (2+n) := by
  have hn := HodgeConjecture.DegreeTwo.SupportedSourceThomNaturality.Constructions.regularSourceThomSupportedRelativeIso_support_naturality D a ha h U n
  have hs := Intrinsic.ThomSupportEquality.relativeComplementChange_eq_congr
    (TopCat.of ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U)) (fun _ hx => h hx) es n
  have ht := Intrinsic.ThomSupportEquality.relativeComplementChange_eq_congr (TopCat.of U)
    (fun _ hx => (sup_le_sup_left h D.regularThomComplementOpen) hx) et (2+n)
  change HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.ClosedSourceRelativeMap.Constructions.closedSourceRelativeSupportChange (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D) h U) n = _ at hs
  change HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.IntersectSupportNaturality.Constructions.relativeOpenComplementChange
    (X := TopCat.of D.regularAmbientSpace) (sup_le_sup_left h D.regularThomComplementOpen) U) (2+n) = _ at ht
  rw [hs, ht] at hn
  apply Iso.ext
  apply (cancel_epi (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr
    (TopCat.of ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj U)) es n).hom).1
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, Category.assoc] using hn

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LocalThomSupportEquality
