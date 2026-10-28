import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.IntersectGlobalComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedThomFunctorModel
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom

/-! # Thom Global Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ThomGlobalComparison

noncomputable section

/-! The constructed global relative Thom map is the native compact Thom pushforward's actual relative stage. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

theorem regularSupportedThomFunctorRelativeIso_native (O : Opens D.regularAmbientSpace) (n : ℕ) :
    SupportedThomFunctorModel.regularSupportedThomFunctorRelativeIso D O n =
      HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso D O ⊤ n ≪≫
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        ((D.regularThomComplementOpen ⊔ O) : Set D.regularAmbientSpace) (2+n) ≪≫
      (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
        (IntersectGlobalComparison.supportUnion_comm O D.regularThomComplementOpen) (2+n)).symm := by
  unfold SupportedThomFunctorModel.regularSupportedThomFunctorRelativeIso
  rw [IntersectGlobalComparison.relativeNestedSupportedCohomologyIso_native]
  apply Iso.ext
  simp only [HodgeConjecture.DegreeTwo.SupportedThomRelative.Constructions.regularThomClosedSupportRelativeIso, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Category.assoc]
  rfl

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_native (O : Opens D.regularAmbientSpace) (n : ℕ) :
    Supported.ThomCupStage.regularSourceThomSupportedRelativeIso D a ha O n =
      HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso D a ha O n ≪≫
      (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
        (IntersectGlobalComparison.supportUnion_comm O D.regularThomComplementOpen) (2+n)).symm := by
  unfold Supported.ThomCupStage.regularSourceThomSupportedRelativeIso
  rw [SupportedResolutionComparison.regularSourceSupportedThomIso_native, SupportedThomFunctorModel.regularSupportedThomGlobalRelativeIso_functor]
  apply Iso.ext
  simp only [Iso.trans_hom, Category.assoc, Functor.mapIso_symm, Iso.symm_hom, Iso.inv_hom_id_assoc]
  have hs := congrArg Iso.hom (SourceGlobalComparison.supportedSourceGlobalCohomologyIso_native D.regularComplementTopCatMap O n)
  have ht := congrArg Iso.hom (regularSupportedThomFunctorRelativeIso_native D O n)
  simp only [Iso.trans_hom, Iso.symm_hom] at hs ht
  erw [← Category.assoc (Supported.SourceCohomology.supportedSourceGlobalCohomologyIso D.regularComplementTopCatMap O n).inv, hs, ht]
  simp only [HodgeConjecture.DegreeTwo.GlobalSupportedSourceThom.Constructions.regularSourceThomSupportedGlobalIso, HodgeConjecture.DegreeTwo.SupportedSourceThomIso.Constructions.regularSourceThomSupportedRelativeIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.ThomGlobalComparison
