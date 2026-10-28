import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularThomSourceSections
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedCupSectionCohomology
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSourceResolution
import OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

/-! # Thom Source -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomSource.Constructions

noncomputable section

section

/-! The canonical source-to-relative isomorphism is the original normalized Thom cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularThomSectionsRelativeIso_eq (U : Opens Z.regularAmbientSpace) (n : ℕ) :
    ThomShiftSections.Constructions.regularThomGoodShiftSectionsRelativeIso Z U n =
      SupportedCupSectionCohomology.Constructions.supportedTwoGoodShiftRelativeIso (TopCat.of Z.regularAmbientSpace)
        Z.regularThomComplementOpen
        (fun i hi => RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z i (by omega)) U n := rfl

theorem regularSourceThomRelativeSectionsIso_cup (U : Opens Z.regularAmbientSpace) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
        (SingularSheafPullback.Constructions.openPreimageMap (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U) 0 ≫
        (RegularThomSourceSections.Constructions.regularSourceThomRelativeSectionsIso Z a ha U).hom =
      ModuleCat.ofHom (CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup (R := ℚ) (TopCat.of U)
        (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U) 2 0
        (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
          (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U 2 Z.regularThomClass)) := by
  rw [← ClosedSourceResolution.Constructions.rationalSourceSheafPullback_sections_cohomology (RegularTopGysin.Constructions.regularSourceInclusionMap V Z) U 0]
  simp only [RegularThomSourceSections.Constructions.regularSourceThomRelativeSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc
    (HomologicalComplex.homologyMap
      (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) (X := TopCat.of Z.regularAmbientSpace) U).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (SingularSheafPullback.Constructions.singularSheafPullbackMap (ModuleCat.of ℚ ℚ) (RegularTopGysin.Constructions.regularSourceInclusionMap V Z))) 0),
    RegularThomSourceSections.Constructions.regularSourceThomSectionsZeroIso_comm]
  rw [regularThomSectionsRelativeIso_eq]
  have h := SupportedCupSectionCohomology.Constructions.relativeTwoCupGoodShiftSheafSections_cohomology
    (TopCat.of Z.regularAmbientSpace) Z.regularThomComplementOpen a
    (fun i hi => RegularThomSheafPurity.Constructions.regularThomSheaf_exactAt_except Z i (by omega)) U 0
  rw [RelativeCupShiftSections.Constructions.relativeTwoCocycleOpenRestriction_class, ha] at h
  exact h

end

section

/-! The actual source constant-one class maps to the original normalized global Thom class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

theorem singularPullback_cupUnit {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of R R) f).f 0 (AlgebraicTopology.Products.Cup.cupUnit (TopCat.toSSet.obj Y)) =
      AlgebraicTopology.Products.Cup.cupUnit (TopCat.toSSet.obj X) := by
  apply AlgebraicTopology.Products.Cup.cochain_ext (TopCat.toSSet.obj X) (ModuleCat.of R R)
  intro s
  exact (AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of R R) (TopCat.toSSet.map f)
    (AlgebraicTopology.Products.Cup.cupUnit (TopCat.toSSet.obj Y)) s).trans
    ((AlgebraicTopology.Products.Cup.evaluation_cupUnit (TopCat.toSSet.obj Y) _).trans
      (AlgebraicTopology.Products.Cup.evaluation_cupUnit (TopCat.toSSet.obj X) s).symm)

theorem singularCohomologyPullback_cupUnit {X Y : TopCat.{0}} (f : X ⟶ Y) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R) f 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit Y) =
      AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit X := by
  change HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.singularPullback (ModuleCat.of R R) f) 0
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (TopCat.toSSet.obj Y))) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (TopCat.toSSet.obj X))
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 0)
  apply Subtype.ext
  exact singularPullback_cupUnit f

theorem relativeAbsoluteCohomologyCup_cupUnit (X : TopCat.{0}) (C : Set X) (p : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of R R) X C p) :
    CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup X C p 0 a (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit X) = a := by
  obtain ⟨a,rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X C) p a
  change CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup X C p 0 (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p a)
    (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 0 (AlgebraicTopology.Products.CupCohomologyAlgebra.cocycleCupUnit (TopCat.toSSet.obj X))) = _
  rw [CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup_class_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ p)
  apply Subtype.ext
  apply CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective (ModuleCat.of R R) X C p
  rw [CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCocycleCupWith_val]
  exact (CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion X C
    (M := ModuleCat.of R R) (N := ModuleCat.of R R) (L := ModuleCat.of R R)
    (LinearMap.mul R R) (p := p) (q := 0) a.val (AlgebraicTopology.Products.Cup.cupUnit (TopCat.toSSet.obj X))).trans
      (AlgebraicTopology.Products.Cup.cup_cupUnit (TopCat.toSSet.obj X)
        ((AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of R R) X C).f p a.val))

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

theorem regularSourceThomRelativeSectionsIso_unit (U : Opens Z.regularAmbientSpace) :
    (RegularThomSourceSections.Constructions.regularSourceThomRelativeSectionsIso Z a ha U).hom
        (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit
          (TopCat.of ((Opens.map (RegularTopGysin.Constructions.regularSourceInclusionMap V Z)).obj U))) =
      CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) U 2 Z.regularThomClass := by
  have h := ConcreteCategory.congr_hom (regularSourceThomRelativeSectionsIso_cup Z a ha U)
    (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℚ) (TopCat.of U))
  rw [ConcreteCategory.comp_apply, singularCohomologyPullback_cupUnit] at h
  exact h.trans (relativeAbsoluteCohomologyCup_cupUnit _ _ _ _)

end

/-! A genuine global source-to-relative Thom isomorphism, with its actual unit normalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Products.CupCohomologyAlgebra

set_option backward.isDefEq.respectTransparency false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
  (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
variable (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a = Z.regularThomClass)

def regularSourceThomGlobalIso :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) 0 ≅
      Z.regularThomGroup :=
  (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAnalyticSpace) 0).symm ≪≫
    RegularThomSourceSections.Constructions.regularSourceThomRelativeSectionsIso Z a ha ⊤ ≪≫
      AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
        (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) 2

theorem regularSourceThomGlobalIso_unit :
    (regularSourceThomGlobalIso Z a ha).hom
      (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (TopCat.of Z.regularAnalyticSpace)) = Z.regularThomClass := by
  have hs : (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAnalyticSpace) 0).inv
      (AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (TopCat.of Z.regularAnalyticSpace)) =
    AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (TopCat.of (⊤ : Opens Z.regularAnalyticSpace)) :=
    singularCohomologyPullback_cupUnit (Opens.inclusionTopIso (TopCat.of Z.regularAnalyticSpace)).hom
  simp only [regularSourceThomGlobalIso, Iso.trans_hom, Iso.symm_hom, ConcreteCategory.comp_apply]
  rw [hs]
  let e := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeCohomologyPresheafTopIso (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace)
    (Z.regularThomComplementOpen : Set Z.regularAmbientSpace) 2
  refine (congrArg (fun c => e.hom c)
    (regularSourceThomRelativeSectionsIso_unit Z a ha ⊤)).trans ?_
  change e.hom (e.inv Z.regularThomClass) = Z.regularThomClass
  exact ConcreteCategory.congr_hom e.inv_hom_id Z.regularThomClass

theorem regularSourceThomGlobalIso_eq
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (Z.regularThomComplementOpen : Set Z.regularAmbientSpace)) 2)
    (hb : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 b = Z.regularThomClass) :
    regularSourceThomGlobalIso Z a ha = regularSourceThomGlobalIso Z b hb := by
  unfold regularSourceThomGlobalIso
  rw [RegularThomSourceSections.Constructions.regularSourceThomRelativeSectionsIso_eq Z a ha b hb ⊤]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomSource.Constructions
