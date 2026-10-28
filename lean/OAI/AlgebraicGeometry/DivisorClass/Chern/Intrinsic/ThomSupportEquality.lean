import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ThomGlobalComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSourceThomNaturality

/-! # Thom Support Equality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ThomSupportEquality

noncomputable section

/-! Equal source and target supports preserve the actual global Thom isomorphism. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSourceThomNaturality.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem relativeComplementChange_eq_congr (X : TopCat.{0}) {A B : Set X}
    (h : A ⊆ B) (e : B = A) (n : ℕ) :
    HomologicalComplex.homologyMap (HodgeConjecture.DegreeTwo.RelativeTopSupportNaturality.Constructions.relativeComplementChange X h) n =
      (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr X e n).hom := by
  subst B
  change AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap X h n = 𝟙 _
  exact AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalSubsetCohomologyMap_refl X A n

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceThomSupportedGlobalIso_supportEquality
    {O P : Opens D.regularAmbientSpace} (h : O ≤ P)
    (es : ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj P : Set D.regularAnalyticSpace) =
      ((Opens.map (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V D)).obj O : Set D.regularAnalyticSpace))
    (et : ((D.regularThomComplementOpen ⊔ P : Opens D.regularAmbientSpace) : Set D.regularAmbientSpace) =
      ((D.regularThomComplementOpen ⊔ O : Opens D.regularAmbientSpace) : Set D.regularAmbientSpace)) (n : ℕ) :
    HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso D a ha O n =
      (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAnalyticSpace) es n).symm ≪≫
      HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso D a ha P n ≪≫
      AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace) et (2+n) := by
  have hn := HodgeConjecture.DegreeTwo.GlobalSourceThomNaturality.Constructions.regularSourceThomSupportedGlobalIso_support_naturality D a ha h n
  rw [relativeComplementChange_eq_congr _ _ es,
    relativeComplementChange_eq_congr _ _ et] at hn
  apply Iso.ext
  apply (cancel_epi (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAnalyticSpace) es n).hom).1
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, Category.assoc] using hn

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ThomSupportEquality
