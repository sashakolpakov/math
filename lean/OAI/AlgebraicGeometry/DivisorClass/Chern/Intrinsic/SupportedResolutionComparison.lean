import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.ThomSourceComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportThomResolution

/-! # Supported Resolution Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SupportedResolutionComparison

noncomputable section

/-! The supported comparison agrees with the native global Thom pushforward's resolution model. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportThomResolution.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O U : Opens X)

theorem supportedSectionsFunctor_eq_native :
    Supported.DerivedComparison.supportedSectionsFunctor O U = HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor O U := rfl

theorem flasqueSupportedDerivedCohomologyIso_native
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (he : ∀ n, K.ExactAt (n+1)) (n : ℕ) :
    Supported.DerivedComparison.flasqueSupportedDerivedCohomologyIso O U K hK he n =
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
        (Supported.DerivedComparison.supportedSectionsFunctorIso O U K) ≪≫ HodgeConjecture.DegreeTwo.ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso O U K hK he n := by
  let I := HodgeConjecture.DegreeTwo.FlasqueDerivedComparison.Constructions.rationalSheafInjectiveResolution (K.homology 0)
  let f := HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he I
  let G := (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)
  let F := (Supported.DerivedComparison.supportedSectionsFunctor O U).mapHomologicalComplex (ComplexShape.up ℕ)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n
  have hn : H.map (G.map (Supported.SectionQuasiIso.supportedSheafComplexMap O f)) ≫
      H.map (Supported.DerivedComparison.supportedSectionsFunctorIso O U I.cocomplex).hom =
    H.map (Supported.DerivedComparison.supportedSectionsFunctorIso O U K).hom ≫ H.map (F.map f) := by
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map (Supported.DerivedComparison.supportedSectionsFunctorIso_naturality O U f)
  apply Iso.ext
  change (H.map (G.map (Supported.SectionQuasiIso.supportedSheafComplexMap O f)) ≫
    H.map (Supported.DerivedComparison.supportedSectionsFunctorIso O U I.cocomplex).hom) ≫
      (I.isoRightDerivedObj (Supported.DerivedComparison.supportedSectionsFunctor O U) n).inv =
    H.map (Supported.DerivedComparison.supportedSectionsFunctorIso O U K).hom ≫
      H.map (F.map f) ≫ (I.isoRightDerivedObj (Supported.DerivedComparison.supportedSectionsFunctor O U) n).inv
  rw [hn, Category.assoc]

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceSupportedThomIso_native (O U : Opens D.regularAmbientSpace) (n : ℕ) :
    Supported.ThomSourceComparison.regularSourceSupportedThomIso D a ha O U n =
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
        (Supported.DerivedComparison.supportedSectionsFunctorIso (X := TopCat.of D.regularAmbientSpace) O U (HodgeConjecture.DegreeTwo.RegularThomSourceSheaf.Constructions.regularSourceSheafComplex D)) ≪≫
      HodgeConjecture.DegreeTwo.ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso D a ha O U n ≪≫
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
        (Supported.DerivedComparison.supportedSectionsFunctorIso (X := TopCat.of D.regularAmbientSpace) O U
          (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex D)).symm := by
  unfold Supported.ThomSourceComparison.regularSourceSupportedThomIso Supported.ThomSourceComparison.derivedSupportedResolutionIso
  rw [flasqueSupportedDerivedCohomologyIso_native, flasqueSupportedDerivedCohomologyIso_native]
  apply Iso.ext
  simp only [HodgeConjecture.DegreeTwo.ClosedSupportThomResolution.Constructions.regularSourceThomClosedSupportIso, HodgeConjecture.DegreeTwo.ClosedSupportThomResolution.Constructions.closedSupportDerivedResolutionIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SupportedResolutionComparison
