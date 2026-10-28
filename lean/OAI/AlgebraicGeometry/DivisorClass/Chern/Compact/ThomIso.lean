import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.ThomCupStage
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.SourceSheafTrace
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomCupSupport

/-! # Thom Iso -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ThomIso

noncomputable section

/-! The source-to-Thom isomorphism retains each actual compact test and its literal intersection with the divisor. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (D : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

def regularThomCompactIntersection (K : Compacts D.regularAmbientSpace) : Compacts D.regularAmbientSpace :=
  HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions.thomCompactIntersection (TopCat.of D.regularAmbientSpace)
    (D.regularThomComplementOpen : Set D.regularAmbientSpace) D.regularThomComplementOpen.isOpen K

theorem regularThomCompactIntersection_complement (K : Compacts D.regularAmbientSpace) :
    ((SourceSheafTrace.compactTestComplement (X := TopCat.of D.regularAmbientSpace) K ⊔ D.regularThomComplementOpen) : Set D.regularAmbientSpace) =
      (regularThomCompactIntersection D K : Set D.regularAmbientSpace)ᶜ := by
  change (K : Set D.regularAmbientSpace)ᶜ ∪ (D.regularThomComplementOpen : Set D.regularAmbientSpace) = _
  rw [Set.union_comm]
  exact HodgeConjecture.DegreeTwo.CompactThomCupSupport.Constructions.thomCompactIntersection_complement (TopCat.of D.regularAmbientSpace)
    (D.regularThomComplementOpen : Set D.regularAmbientSpace) D.regularThomComplementOpen.isOpen K

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of D.regularAmbientSpace) (D.regularThomComplementOpen : Set D.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = D.regularThomClass)

def regularSourceCompactThomIso (K : Compacts D.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAnalyticSpace)
      (AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.properCompactPreimage D.regularComplementTopCatMap
        D.isProperMap_regularComplementTopCatMap K : Set D.regularAnalyticSpace)ᶜ n ≅
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (regularThomCompactIntersection D K : Set D.regularAmbientSpace)ᶜ (2+n) :=
  Supported.ThomCupStage.regularSourceThomSupportedRelativeIso D a ha (SourceSheafTrace.compactTestComplement (X := TopCat.of D.regularAmbientSpace) K) n ≪≫
    AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
      (regularThomCompactIntersection_complement D K) (2+n)

def regularSheafCompactThomCup (K : Compacts D.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (K : Set D.regularAmbientSpace)ᶜ n ⟶
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
      (regularThomCompactIntersection D K : Set D.regularAmbientSpace)ᶜ (2+n) :=
  HomologicalComplex.homologyMap
      (AlgebraicTopology.Cohomology.Singular.SupportedRelativeComparison.relativeToSupportedSheafGlobalSections (ModuleCat.of ℚ ℚ) (TopCat.of D.regularAmbientSpace)
        (SourceSheafTrace.compactTestComplement (X := TopCat.of D.regularAmbientSpace) K)) n ≫
    HomologicalComplex.homologyMap
      (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of D.regularAmbientSpace) ⊤).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (Supported.SectionQuasiIso.supportedSheafComplexMap (X := TopCat.of D.regularAmbientSpace) (SourceSheafTrace.compactTestComplement (X := TopCat.of D.regularAmbientSpace) K)
          (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of D.regularAmbientSpace)
            D.regularThomComplementOpen a))) n ≫
      (Supported.ThomCupStage.regularSupportedThomGlobalRelativeIso D (SourceSheafTrace.compactTestComplement (X := TopCat.of D.regularAmbientSpace) K) n).hom ≫
      (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
        (regularThomCompactIntersection_complement D K) (2+n)).hom

theorem regularSheafCompactThomCup_factorization (K : Compacts D.regularAmbientSpace) (n : ℕ) :
    AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback (ModuleCat.of ℚ ℚ) D.regularComplementTopCatMap
        D.isProperMap_regularComplementTopCatMap K n ≫ (regularSourceCompactThomIso D a ha K n).hom =
      regularSheafCompactThomCup D a K n := by
  have h := congrArg (fun g => g ≫
    (AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of D.regularAmbientSpace)
      (regularThomCompactIntersection_complement D K) (2+n)).hom)
    (Supported.ThomCupStage.regularSourceThomSupportedRelativeIso_pullback D a ha (SourceSheafTrace.compactTestComplement (X := TopCat.of D.regularAmbientSpace) K) n)
  simpa only [regularSourceCompactThomIso, regularSheafCompactThomCup,
    Iso.trans_hom, Category.assoc, AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStageCohomologyPullback,
    AlgebraicTopology.Duality.Poincare.ProperCompactSupportPullback.compactSupportProperStagePullback, SourceSheafTrace.compactTestComplement] using h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.ThomIso
