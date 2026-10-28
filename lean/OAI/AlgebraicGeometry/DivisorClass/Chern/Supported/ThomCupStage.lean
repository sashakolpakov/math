import OAI.AlgebraicGeometry.DivisorClass.Chern.ClosedSupportIntersection
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.FlasqueExactness
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.ThomSourceComparison
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.RegularCycleFundamentalClass

/-! # Thom Cup Stage -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.ThomCupStage

noncomputable section

section

/-! The supported source-to-Thom comparison has the original relative singular cohomology groups at both ends. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)

def regularSupportedThomGlobalRelativeIso (O : Opens Z.regularAmbientSpace) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex ⊤
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z))).homology n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
      ((O ⊔ Z.regularThomComplementOpen) : Set Z.regularAmbientSpace) (2*p+n) := by
  have := AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.quasiIso_relativeToSupportedSheafGlobalSections_of_metrizable ℚ
    (TopCat.of Z.regularAmbientSpace) (O ⊔ Z.regularThomComplementOpen)
  exact FlasqueExactness.supportedGoodShiftCohomologyIso (X := TopCat.of Z.regularAmbientSpace) O ⊤
      Z.regularThomSheafComplex
      (CycleClass.Geometric.GlobalSupportPurity.Cycles.supportedSingularSheaf_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
        (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen)
      (2*p) (fun i hi => HodgeConjecture.DegreeTwo.RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z i (by omega)) n ≪≫
    (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) (2*p+n)).mapIso
      (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace)
        (⊤ : Opens Z.regularAmbientSpace)).mapHomologicalComplex
        (ComplexShape.up ℕ)).mapIso
        (ClosedSupportIntersection.supportedIntersectionComplexIso (X := TopCat.of Z.regularAmbientSpace) O Z.regularThomComplementOpen
          (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafifiedCochainComplex (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ)
            (TopCat.of Z.regularAmbientSpace))))) ≪≫
    (isoOfQuasiIsoAt
      (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (O ⊔ Z.regularThomComplementOpen)) (2*p+n)).symm

variable (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

def regularSourceThomSupportedRelativeIso (O : Opens D.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAnalyticSpace)
        (((Opens.map D.regularComplementTopCatMap).obj O) : Set D.regularAnalyticSpace) n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      ((O ⊔ D.regularThomComplementOpen) : Set D.regularAmbientSpace) (2+n) :=
  (SourceCohomology.supportedSourceGlobalCohomologyIso D.regularComplementTopCatMap O n).symm ≪≫
    ThomSourceComparison.regularSourceSupportedThomIso D a ha O ⊤ n ≪≫ regularSupportedThomGlobalRelativeIso D O n

theorem regularSourceThomSupportedRelativeIso_eq
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
    (hb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b = D.regularThomClass) (O : Opens D.regularAmbientSpace) (n : ℕ) :
    regularSourceThomSupportedRelativeIso D a ha O n =
      regularSourceThomSupportedRelativeIso D b hb O n := by
  unfold regularSourceThomSupportedRelativeIso ThomSourceComparison.regularSourceSupportedThomIso
  rw [HodgeConjecture.DegreeTwo.ThomResolutionDiagram.Constructions.regularSourceThomZeroSheafIso_eq D a b ha hb]

end

/-! Native relative source pullback factors the actual supported Thom cup at every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

theorem regularSourceThomSupportedRelativeIso_pullback
    (O : Opens D.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
        (A := (((Opens.map D.regularComplementTopCatMap).obj O) : Set D.regularAnalyticSpace))
        (B := (O : Set D.regularAmbientSpace)) (fun _ hy => hy) n ≫
        (regularSourceThomSupportedRelativeIso D a ha O n).hom =
      HomologicalComplex.homologyMap
        (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace) O) n ≫
      HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of D.regularAmbientSpace) ⊤).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
          (SectionQuasiIso.supportedSheafComplexMap (X := TopCat.of D.regularAmbientSpace) O
            (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of D.regularAmbientSpace)
              D.regularThomComplementOpen a))) n ≫
        (regularSupportedThomGlobalRelativeIso D O n).hom := by
  let e := SourceCohomology.supportedSourceGlobalCohomologyIso D.regularComplementTopCatMap O n
  let t := ThomSourceComparison.regularSourceSupportedThomIso D a ha O ⊤ n
  let v := regularSupportedThomGlobalRelativeIso D O n
  let F := (CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of D.regularAmbientSpace) ⊤).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let s := HomologicalComplex.homologyMap
    (F.map (SourcePullback.supportedSourcePullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap O)) n
  have hc : s ≫ t.hom = HomologicalComplex.homologyMap
      (F.map (SectionQuasiIso.supportedSheafComplexMap (X := TopCat.of D.regularAmbientSpace) O
        (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of D.regularAmbientSpace)
          D.regularThomComplementOpen a))) n :=
    ThomSourceComparison.regularSourceSupportedThomIso_cup D a ha O ⊤ n
  rw [← SourcePullback.supportedSourcePullback_cohomology D.regularComplementTopCatMap O n]
  change (_ ≫ s ≫ e.hom) ≫ (e.inv ≫ t.hom ≫ v.hom) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc s t.hom, hc]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.ThomCupStage
