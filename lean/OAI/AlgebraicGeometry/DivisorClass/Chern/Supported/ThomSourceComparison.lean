import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.DerivedNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SourcePullback
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AllThomSource

/-! # Thom Source Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.ThomSourceComparison

noncomputable section

/-! The actual source and Thom resolutions agree in all supported degrees and preserve the original cup map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AllThomSource.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section General

variable {X : TopCat.{0}} (O U : Opens X)
variable (K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (heK : ∀ n, K.ExactAt (n+1))
variable (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (heL : ∀ n, L.ExactAt (n+1))

def derivedSupportedResolutionIso (e : K.homology 0 ≅ L.homology 0) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K)).homology n ≅
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O L)).homology n :=
  DerivedComparison.flasqueSupportedDerivedCohomologyIso O U K hK heK n ≪≫
    ((DerivedComparison.supportedSectionsFunctor O U).rightDerived n).mapIso e ≪≫
    (DerivedComparison.flasqueSupportedDerivedCohomologyIso O U L hL heL n).symm

theorem derivedSupportedResolutionIso_comm
    (A : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hA : ∀ n, TopCat.Sheaf.IsFlasque (A.X n)) (heA : ∀ n, A.ExactAt (n+1))
    (f : A ⟶ K) (g : A ⟶ L) (e : K.homology 0 ≅ L.homology 0)
    (he : HomologicalComplex.homologyMap f 0 ≫ e.hom = HomologicalComplex.homologyMap g 0)
    (n : ℕ) :
    HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SectionQuasiIso.supportedSheafComplexMap O f)) n ≫
        (derivedSupportedResolutionIso O U K L hK heK hL heL e n).hom =
      HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SectionQuasiIso.supportedSheafComplexMap O g)) n := by
  apply (cancel_mono (DerivedComparison.flasqueSupportedDerivedCohomologyIso O U L hL heL n).hom).mp
  simp only [derivedSupportedResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, DerivedNaturality.flasqueSupportedDerivedCohomologyIso_naturality O U f hA heA hK heK,
    Category.assoc, ← Functor.map_comp, he,
    DerivedNaturality.flasqueSupportedDerivedCohomologyIso_naturality O U g hA heA hL heL]

end General

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceSupportedThomIso (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O (HodgeConjecture.DegreeTwo.RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z))).homology n ≅
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z))).homology n :=
  derivedSupportedResolutionIso (X := TopCat.of Z.regularAmbientSpace) O U
    (HodgeConjecture.DegreeTwo.RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z) (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V Z)) (HodgeConjecture.DegreeTwo.AllThomSource.Constructions.regularSourceSheaf_exact_positive Z)
    (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z) (HodgeConjecture.DegreeTwo.AllThomSource.Constructions.regularThomGoodShift_exact_positive Z)
    (HodgeConjecture.DegreeTwo.RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha) n

theorem regularSourceSupportedThomIso_cup (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SourcePullback.supportedSourcePullback (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V Z) O)) n ≫
        (regularSourceSupportedThomIso Z a ha O U n).hom =
      HomologicalComplex.homologyMap
        (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (SectionQuasiIso.supportedSheafComplexMap O
            (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
              Z.regularThomComplementOpen a))) n := by
  have := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace V.analyticModel Z.regularAmbientSpace
  exact derivedSupportedResolutionIso_comm (X := TopCat.of Z.regularAmbientSpace) O U
    (HodgeConjecture.DegreeTwo.RegularThomSourceSheaf.Constructions.regularSourceSheafComplex Z) (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V Z)) (HodgeConjecture.DegreeTwo.AllThomSource.Constructions.regularSourceSheaf_exact_positive Z)
    (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z) (HodgeConjecture.DegreeTwo.AllThomSource.Constructions.regularThomGoodShift_exact_positive Z)
    (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of Z.regularAmbientSpace))
    (AlgebraicTopology.Cohomology.Singular.SheafFlasque.sheafifiedSingularCochains_isFlasque_of_metrizable (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace))
    (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheaf_positive_exact (TopCat.of Z.regularAmbientSpace))
    (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (HodgeConjecture.DegreeTwo.RegularTopGysin.Constructions.regularSourceInclusionMap V Z))
    (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen a)
    (HodgeConjecture.DegreeTwo.RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso Z a ha) (HodgeConjecture.DegreeTwo.RegularThomSourceSheaf.Constructions.regularSourceThomZeroSheafIso_comm Z a ha) n

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.ThomSourceComparison
