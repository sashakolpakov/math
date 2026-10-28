import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomCupStalk
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalStalkQuasiIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSourceSheafComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceResolution
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularTopGysin

/-! # Regular Thom Source Sheaf -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomSourceSheaf.Constructions

noncomputable section

section

/-! The normalized Thom sheaf is canonically the independently constructed source cohomology sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

theorem sheafHomologyMap_stalk_isIso {R : Type} [Ring R] {X : TopCat.{0}}
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} R) X) ℕ}
    (f : K ⟶ L) (x : X) (n : ℕ) [QuasiIsoAt (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainMap f x) n] :
    IsIso ((LocalStalkQuasiIso.Constructions.moduleSheafStalk x).map (HomologicalComplex.homologyMap f n)) := by
  have : IsIso ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso K x n).hom ≫
      (LocalStalkQuasiIso.Constructions.moduleSheafStalk x).map (HomologicalComplex.homologyMap f n)) := by
    change IsIso ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso K x n).hom ≫
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x).map
        (HomologicalComplex.homologyMap f n).hom)
    rw [← AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso K x n).hom _

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)

abbrev regularSourceSheafComplex :=
  SingularSheafPullback.Constructions.singularPushforwardSheafComplex (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)

def regularSourceZeroSheafMap :=
  HomologicalComplex.homologyMap
    (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)) 0

theorem regularSourceZeroSheafMap_stalk_isIso (x : Z.regularAnalyticSpace) :
    IsIso ((LocalStalkQuasiIso.Constructions.moduleSheafStalk (Z.regularComplementInclusion x)).map (regularSourceZeroSheafMap Z)) := by
  have := NormalSourceSheafComparison.Constructions.normalPairSourceSheafPullback_stalk_quasiIso
    (f := RegularTopGysin.Constructions.regularSourceInclusionMap V Z) (Z.regularFixedNormalPair x)
    Z.isClosedEmbedding_regularComplementInclusion.isEmbedding
  exact sheafHomologyMap_stalk_isIso _ _ 0

theorem regularSourceZeroSheaf_stalk_isZero (y : Z.regularAmbientSpace)
    (hy : y ∉ Set.range Z.regularComplementInclusion) :
    IsZero ((LocalStalkQuasiIso.Constructions.moduleSheafStalk y).obj ((regularSourceSheafComplex Z).homology 0)) := by
  have hz : IsZero ((AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCochainComplex (regularSourceSheafComplex Z) y).homology 0) :=
    (ClosedPushforwardExactness.Constructions.closedPushforwardSheafComplex_stalk_exactAt (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)
      Z.isClosedEmbedding_regularComplementInclusion (SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex
        (TopCat.of Z.regularAnalyticSpace)) y hy 0).isZero_homology
  exact hz.of_iso (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso (regularSourceSheafComplex Z) y 0).symm

theorem regularThomGoodShiftZeroSheaf_stalk_isZero (y : Z.regularAmbientSpace)
    (hy : y ∉ Set.range Z.regularComplementInclusion) :
    IsZero ((LocalStalkQuasiIso.Constructions.moduleSheafStalk y).obj ((GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z).homology 0)) := by
  have hz : IsZero ((LocalStalkQuasiIso.Constructions.moduleSheafStalk y).obj (Z.regularThomSheafComplex.homology 2)) :=
    (CycleClass.Geometric.SupportStalkVanishes.Cycles.supportedSingularSheaf_stalk_homology_isZero_of_mem
      (X := TopCat.of Z.regularAmbientSpace) (ModuleCat.of ℚ ℚ)
      Z.regularThomComplementOpen y hy 2).of_iso
        (AlgebraicTopology.Cohomology.Singular.SheafQuasiIso.sheafStalkCohomologyIso Z.regularThomSheafComplex y 2).symm
  exact hz.of_iso ((LocalStalkQuasiIso.Constructions.moduleSheafStalk y).mapIso (GoodShiftCohomology.Constructions.regularThomGoodShift_zeroHomologyIso Z))

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularThomZeroSheafMap :=
  HomologicalComplex.homologyMap (RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap
    (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen a) 0

include ha

theorem regularThomZeroSheafMap_stalk_isIso (x : Z.regularAnalyticSpace) :
    IsIso ((LocalStalkQuasiIso.Constructions.moduleSheafStalk (Z.regularComplementInclusion x)).map (regularThomZeroSheafMap Z a)) := by
  have := RegularThomCupStalk.Constructions.regularThomCupGoodShiftSheaf_stalk_quasiIso Z a ha x
  exact sheafHomologyMap_stalk_isIso _ _ 0

theorem regularSourceThom_localQuotients (y : Z.regularAmbientSpace) :
    (IsIso ((LocalStalkQuasiIso.Constructions.moduleSheafStalk y).map (regularSourceZeroSheafMap Z)) ∧
      IsIso ((LocalStalkQuasiIso.Constructions.moduleSheafStalk y).map (regularThomZeroSheafMap Z a))) ∨
    (IsZero ((LocalStalkQuasiIso.Constructions.moduleSheafStalk y).obj ((regularSourceSheafComplex Z).homology 0)) ∧
      IsZero ((LocalStalkQuasiIso.Constructions.moduleSheafStalk y).obj ((GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z).homology 0))) := by
  by_cases hy : y ∈ Set.range Z.regularComplementInclusion
  · obtain ⟨x,rfl⟩ := hy
    exact Or.inl ⟨regularSourceZeroSheafMap_stalk_isIso Z x,
      regularThomZeroSheafMap_stalk_isIso Z a ha x⟩
  · exact Or.inr ⟨regularSourceZeroSheaf_stalk_isZero Z y hy,
      regularThomGoodShiftZeroSheaf_stalk_isZero Z y hy⟩

/-- Both sides were constructed independently; the actual normalized cup identifies them. -/
def regularSourceThomZeroSheafIso :
    (regularSourceSheafComplex Z).homology 0 ≅ (GoodShiftCohomology.Constructions.regularThomGoodShiftSheafComplex Z).homology 0 :=
  LocalStalkQuasiIso.Constructions.moduleSheafLocalQuotientIso (regularSourceZeroSheafMap Z) (regularThomZeroSheafMap Z a)
    (regularSourceThom_localQuotients Z a ha)

theorem regularSourceThomZeroSheafIso_comm :
    regularSourceZeroSheafMap Z ≫ (regularSourceThomZeroSheafIso Z a ha).hom =
      regularThomZeroSheafMap Z a :=
  LocalStalkQuasiIso.Constructions.moduleSheafLocalQuotientIso_comm _ _ _

def regularSourceThomSheafIso :
    (regularSourceSheafComplex Z).homology 0 ≅ Z.regularThomSheafComplex.homology 2 :=
  regularSourceThomZeroSheafIso Z a ha ≪≫ GoodShiftCohomology.Constructions.regularThomGoodShift_zeroHomologyIso Z

end

/-! Left exact section functors preserve degree-zero cohomology and its actual comparison maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

theorem cochain_zero_incoming (K : CochainComplex C ℕ) : (K.sc 0).f=0 := by
  change K.d ((ComplexShape.up ℕ).prev 0) 0 = 0
  simp

local instance zeroLeftHomology (K : CochainComplex C ℕ) : F.PreservesLeftHomologyOf (K.sc 0) :=
  F.preservesLeftHomology_of_zero_f (K.sc 0) (cochain_zero_incoming K)

local instance zeroRightHomology (K : CochainComplex C ℕ) : F.PreservesRightHomologyOf (K.sc 0) :=
  F.preservesRightHomology_of_zero_f (K.sc 0) (cochain_zero_incoming K)

def leftExactZeroCohomologyIso (K : CochainComplex C ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology 0 ≅ F.obj (K.homology 0) :=
  (K.sc 0).mapHomologyIso F

theorem leftExactZeroCohomologyIso_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map f) 0 ≫
        (leftExactZeroCohomologyIso F L).hom =
      (leftExactZeroCohomologyIso F K).hom ≫ F.map (HomologicalComplex.homologyMap f 0) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℕ) 0).map f) F

def zeroSectionComparisonIso (K L : CochainComplex C ℕ) (e : K.homology 0 ≅ L.homology 0) :
    ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology 0 ≅
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).homology 0 :=
  leftExactZeroCohomologyIso F K ≪≫ F.mapIso e ≪≫ (leftExactZeroCohomologyIso F L).symm

theorem zeroSectionComparisonIso_comm {A K L : CochainComplex C ℕ}
    (f : A ⟶ K) (g : A ⟶ L) (e : K.homology 0 ≅ L.homology 0)
    (he : HomologicalComplex.homologyMap f 0 ≫ e.hom = HomologicalComplex.homologyMap g 0) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map f) 0 ≫
        (zeroSectionComparisonIso F K L e).hom =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map g) 0 := by
  apply (cancel_mono (leftExactZeroCohomologyIso F L).hom).mp
  simp only [zeroSectionComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.mapIso_hom]
  rw [← Category.assoc, leftExactZeroCohomologyIso_naturality,
    Category.assoc, ← Functor.map_comp, he, leftExactZeroCohomologyIso_naturality]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomSourceSheaf.Constructions
