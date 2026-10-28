import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ThomSupportEquality
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ImageSupport

/-! # Compact Thom Stage -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.CompactThomStage

noncomputable section

/-! ChernClass's compact Thom comparison is the actual compact stage of the native Thom pushforward. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceCompactThomIso_native (K : Compacts D.regularAmbientSpace) (n : ℕ) :
    Compact.ThomIso.regularSourceCompactThomIso D a ha K n =
      HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso D a ha
        (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage D.regularComplementTopCatMap D.isProperMap_regularComplementTopCatMap K) n ≪≫
      AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
        (congrArg (fun J : Compacts D.regularAmbientSpace => (J : Set D.regularAmbientSpace)ᶜ)
          (Compact.ImageSupport.regularCompactImage_preimage D K)) (2+n) := by
  let L := AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage D.regularComplementTopCatMap D.isProperMap_regularComplementTopCatMap K
  have hs := HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularCompactImageComplement_preimage D L
  have ht := (Compact.ImageSupport.regularCompactImagePreimage_unionComplement D K).symm
  have hn := ThomSupportEquality.regularSourceThomSupportedGlobalIso_supportEquality D a ha
    (Compact.ImageSupport.compactTestComplement_le_imagePreimageComplement D K) hs ht n
  unfold Compact.ThomIso.regularSourceCompactThomIso
  rw [ThomGlobalComparison.regularSourceThomSupportedRelativeIso_native, hn]
  apply Iso.ext
  simp only [HodgeConjecture.DegreeTwo.RegularCompactThomStage.Constructions.regularSourceCompactThomStageIso, Iso.trans_hom, Iso.symm_hom,
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.CompactThomStage
