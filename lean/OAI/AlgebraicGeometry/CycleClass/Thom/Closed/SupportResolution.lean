import OAI.AlgebraicGeometry.CycleClass.Thom.AllDegreeSource
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportComparison

/-! # Support Resolution -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportResolution.Constructions.HigherThom

noncomputable section

/-! The coherent source–Thom comparison retains every specified closed support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportComparison.Constructions

set_option backward.isDefEq.respectTransparency false

section General

variable {X : TopCat.{0}} (O U : Opens X)
variable (K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (heK : ∀ n, K.ExactAt (n+1))
variable (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) (heL : ∀ n, L.ExactAt (n+1))

def closedSupportDerivedResolutionIso (e : K.homology 0 ≅ L.homology 0) (n : ℕ) :
    (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n ≅
      (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U).mapHomologicalComplex (ComplexShape.up ℕ)).obj L).homology n :=
  HodgeConjecture.DegreeTwo.ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso O U K hK heK n ≪≫
    ((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U).rightDerived n).mapIso e ≪≫
    (HodgeConjecture.DegreeTwo.ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso O U L hL heL n).symm

theorem closedSupportDerivedResolutionIso_comm
    (A : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
    (hA : ∀ n, TopCat.Sheaf.IsFlasque (A.X n)) (heA : ∀ n, A.ExactAt (n+1))
    (f : A ⟶ K) (g : A ⟶ L) (e : K.homology 0 ≅ L.homology 0)
    (he : HomologicalComplex.homologyMap f 0 ≫ e.hom = HomologicalComplex.homologyMap g 0) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U).mapHomologicalComplex (ComplexShape.up ℕ)).map f) n ≫
        (closedSupportDerivedResolutionIso O U K L hK heK hL heL e n).hom =
      HomologicalComplex.homologyMap
        (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := X) O U).mapHomologicalComplex (ComplexShape.up ℕ)).map g) n := by
  apply (cancel_mono (HodgeConjecture.DegreeTwo.ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso O U L hL heL n).hom).mp
  simp only [closedSupportDerivedResolutionIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, HodgeConjecture.DegreeTwo.ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso_naturality O U hA heA f hK heK,
    Category.assoc, ← Functor.map_comp, he,
    HodgeConjecture.DegreeTwo.ClosedSupportComparison.Constructions.closedSupportResolutionDerivedIso_naturality O U hA heA g hL heL]

end General

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularSourceThomClosedSupportIso (O U : Opens Z.regularAmbientSpace) (n : ℕ) :=
  closedSupportDerivedResolutionIso (X := TopCat.of Z.regularAmbientSpace) O U (Regular.SourceSheaf.Constructions.HigherThom.regularSourceSheafComplex Z) (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)) (AllDegreeSource.Constructions.HigherThom.regularSourceSheaf_exact_positive Z)
    (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z) (AllDegreeSource.Constructions.HigherThom.regularThomGoodShift_exact_positive Z)
    (Regular.SourceSheaf.Constructions.HigherThom.regularSourceThomZeroSheafIso Z a ha) n

theorem regularSourceThomClosedSupportIso_cup (O U : Opens Z.regularAmbientSpace) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z))) n ≫
        (regularSourceThomClosedSupportIso Z a ha O U n).hom =
      HomologicalComplex.homologyMap
        (((HodgeConjecture.DegreeTwo.ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) O U).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace)
            Z.regularThomComplementOpen a)) n :=
  closedSupportDerivedResolutionIso_comm (X := TopCat.of Z.regularAmbientSpace) O U
    (Regular.SourceSheaf.Constructions.HigherThom.regularSourceSheafComplex Z) (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z)
    (HodgeConjecture.DegreeTwo.ClosedSourceResolution.Constructions.closedSourceSheaf_isFlasque (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z)) (AllDegreeSource.Constructions.HigherThom.regularSourceSheaf_exact_positive Z)
    (HodgeConjecture.DegreeTwo.ThomGoodShiftFlasque.Constructions.regularThomGoodShift_isFlasque Z) (AllDegreeSource.Constructions.HigherThom.regularThomGoodShift_exact_positive Z)
    (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex (TopCat.of Z.regularAmbientSpace))
    (AllDegreeSource.Constructions.HigherThom.regularAmbientSingularSheaf_isFlasque Z) (AllDegreeSource.Constructions.HigherThom.regularAmbientSingularSheaf_exact_positive Z)
    (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (Regular.SourceSheaf.Constructions.HigherThom.regularSourceInclusionMap V Z))
    (EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen a)
    (Regular.SourceSheaf.Constructions.HigherThom.regularSourceThomZeroSheafIso Z a ha) (Regular.SourceSheaf.Constructions.HigherThom.regularSourceThomZeroSheafIso_comm Z a ha) n

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Closed.SupportResolution.Constructions.HigherThom
