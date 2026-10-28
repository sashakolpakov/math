import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.CupStalk
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalStalkQuasiIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSourceSheafComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceResolution

/-! # Source Sheaf -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SourceSheaf.Constructions.HigherThom

noncomputable section

/-! The normalized Thom sheaf is canonically the independently constructed source cohomology sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem sheafHomologyMap_stalk_isIso {R : Type} [Ring R] {X : TopCat.{0}}
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ}
    (f : K ⟶ L) (x : X) (n : ℕ) [QuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainMap f x) n] :
    IsIso ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk x).map (HomologicalComplex.homologyMap f n)) := by
  have : IsIso ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso K x n).hom ≫
      (HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk x).map (HomologicalComplex.homologyMap f n)) := by
    change IsIso ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso K x n).hom ≫
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x).map
        (HomologicalComplex.homologyMap f n).hom)
    rw [← AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso K x n).hom _

abbrev regularSourceInclusionMap (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    TopCat.of Z.regularAnalyticSpace ⟶ TopCat.of Z.regularAmbientSpace :=
  TopCat.ofHom ⟨Z.regularComplementInclusion, Z.continuous_regularComplementInclusion⟩

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : Geometric.DimensionCycles.DimensionCycleSupport V p)

abbrev regularSourceSheafComplex :=
  HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) (regularSourceInclusionMap V Z)

def regularSourceZeroSheafMap :=
  HomologicalComplex.homologyMap
    (HodgeConjecture.DegreeTwo.SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (regularSourceInclusionMap V Z)) 0

theorem regularSourceZeroSheafMap_stalk_isIso (x : Z.regularAnalyticSpace) :
    IsIso ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk (Z.regularComplementInclusion x)).map (regularSourceZeroSheafMap Z)) := by
  have := HodgeConjecture.DegreeTwo.NormalSourceSheafComparison.Constructions.normalPairSourceSheafPullback_stalk_quasiIso
    (f := regularSourceInclusionMap V Z) (Z.regularFixedNormalPair x)
    Z.isClosedEmbedding_regularComplementInclusion.isEmbedding
  exact sheafHomologyMap_stalk_isIso _ _ 0

theorem regularSourceZeroSheaf_stalk_isZero (y : Z.regularAmbientSpace)
    (hy : y ∉ Set.range Z.regularComplementInclusion) :
    IsZero ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk y).obj ((regularSourceSheafComplex Z).homology 0)) := by
  have hz : IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex (regularSourceSheafComplex Z) y).homology 0) :=
    (HodgeConjecture.DegreeTwo.ClosedPushforwardExactness.Constructions.closedPushforwardSheafComplex_stalk_exactAt (regularSourceInclusionMap V Z)
      Z.isClosedEmbedding_regularComplementInclusion (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex
        (TopCat.of Z.regularAnalyticSpace)) y hy 0).isZero_homology
  exact hz.of_iso (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso (regularSourceSheafComplex Z) y 0).symm

theorem regularThomGoodShiftZeroSheaf_stalk_isZero (y : Z.regularAmbientSpace)
    (hy : y ∉ Set.range Z.regularComplementInclusion) :
    IsZero ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk y).obj ((HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z).homology 0)) := by
  have hz : IsZero ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk y).obj (Z.regularThomSheafComplex.homology (2 * p))) :=
    (Geometric.SupportStalkVanishes.Cycles.supportedSingularSheaf_stalk_homology_isZero_of_mem
      (X := TopCat.of Z.regularAmbientSpace) (ModuleCat.of ℚ ℚ)
      Z.regularThomComplementOpen y hy (2 * p)).of_iso
        (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso Z.regularThomSheafComplex y (2 * p)).symm
  exact hz.of_iso ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk y).mapIso (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShift_zeroHomologyIso Z))

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) (2 * p))
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)

def regularThomZeroSheafMap :=
  HomologicalComplex.homologyMap (EvenCupSheaf.Constructions.relativeEvenCupGoodShiftSheafMap
    (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen a) 0

include ha

theorem regularThomZeroSheafMap_stalk_isIso (x : Z.regularAnalyticSpace) :
    IsIso ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk (Z.regularComplementInclusion x)).map (regularThomZeroSheafMap Z a)) := by
  have := CupStalk.Constructions.HigherThom.regularThomCupGoodShiftSheaf_stalk_quasiIso Z a ha x
  exact sheafHomologyMap_stalk_isIso _ _ 0

theorem regularSourceThom_localQuotients (y : Z.regularAmbientSpace) :
    (IsIso ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk y).map (regularSourceZeroSheafMap Z)) ∧
      IsIso ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk y).map (regularThomZeroSheafMap Z a))) ∨
    (IsZero ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk y).obj ((regularSourceSheafComplex Z).homology 0)) ∧
      IsZero ((HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafStalk y).obj ((HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z).homology 0))) := by
  by_cases hy : y ∈ Set.range Z.regularComplementInclusion
  · obtain ⟨x,rfl⟩ := hy
    exact Or.inl ⟨regularSourceZeroSheafMap_stalk_isIso Z x,
      regularThomZeroSheafMap_stalk_isIso Z a ha x⟩
  · exact Or.inr ⟨regularSourceZeroSheaf_stalk_isZero Z y hy,
      regularThomGoodShiftZeroSheaf_stalk_isZero Z y hy⟩

/-- Both sides were constructed independently; the actual normalized cup identifies them. -/
def regularSourceThomZeroSheafIso :
    (regularSourceSheafComplex Z).homology 0 ≅ (HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z).homology 0 :=
  HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafLocalQuotientIso (regularSourceZeroSheafMap Z) (regularThomZeroSheafMap Z a)
    (regularSourceThom_localQuotients Z a ha)

theorem regularSourceThomZeroSheafIso_comm :
    regularSourceZeroSheafMap Z ≫ (regularSourceThomZeroSheafIso Z a ha).hom =
      regularThomZeroSheafMap Z a :=
  HodgeConjecture.DegreeTwo.LocalStalkQuasiIso.Constructions.moduleSheafLocalQuotientIso_comm _ _ _

def regularSourceThomSheafIso :
    (regularSourceSheafComplex Z).homology 0 ≅ Z.regularThomSheafComplex.homology (2 * p) :=
  regularSourceThomZeroSheafIso Z a ha ≪≫ HodgeConjecture.DegreeTwo.GoodShiftCohomology.Constructions.regularThomGoodShift_zeroHomologyIso Z

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SourceSheaf.Constructions.HigherThom
