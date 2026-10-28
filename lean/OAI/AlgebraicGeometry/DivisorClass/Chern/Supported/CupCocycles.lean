import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.CochainUnit
import OAI.AlgebraicGeometry.DivisorClass.Chern.GoodShiftFunctorRepresentatives

/-! # Cup Cocycles -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.CupCocycles

noncomputable section

section

/-! Actual supported cup cocycles retain their native relative representatives through the good shift. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def cochainUnrestrictedCocycle {R : Type} [Ring R]
    (K : CochainComplex (ModuleCat.{0} R) ℕ) (k n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (K.restriction (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K (k+n) :=
  ⟨c.val, by
    rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
    exact (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (K.restriction (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k)) n c.val).mp c.property⟩

variable (X : TopCat.{0}) (C O : Opens X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) 2)

def supportedRelativeTwoCupCocycle (n : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (HodgeConjecture.DegreeTwo.GoodShiftFunctor.Constructions.functorCochainComplex (DerivedComparison.supportedSectionsFunctor O ⊤)
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C)) (2+n) :=
  cochainUnrestrictedCocycle _ 2 n
    (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
      (((DerivedComparison.supportedSectionsFunctor O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupSheafMap X C a)) n
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (CochainUnit.relativeToSupportedFunctorGlobalSections O) n b))

theorem supportedRelativeTwoCupCocycle_forget (n : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) n) :
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap
      (((DerivedComparison.supportedSectionsFunctor O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X))) (2+n)
      (supportedRelativeTwoCupCocycle X C O a n b) =
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (CochainUnit.relativeToSupportedFunctorGlobalSections O) (2+n)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCocycleCupWith X (O : Set X)
        (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
        (LinearMap.mul ℚ ℚ) 2 n
        (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (C : Set X)) 2 a) b) := by
  apply Subtype.ext
  exact CochainUnit.supportedRelativeTwoCup_forget_value X C O a n b.val

variable (hF : ∀ n, (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2).BoundaryGE n →
  (DerivedComparison.supportedSectionsFunctor O ⊤).PreservesRightHomologyOf
    ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C).sc (2+n)))

theorem supportedRelativeTwoCupCocycle_goodShift_class (n : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) n) :
    (GoodShiftFunctorRepresentatives.goodShiftFunctorHomologyIso (DerivedComparison.supportedSectionsFunctor O ⊤)
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) 2 hF n).hom
      (HomologicalComplex.homologyMap
        (((DerivedComparison.supportedSectionsFunctor O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X C a)) n
        (HomologicalComplex.homologyMap (CochainUnit.relativeToSupportedFunctorGlobalSections O) n
          (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n b))) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2+n) (supportedRelativeTwoCupCocycle X C O a n b) := by
  rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality]
  exact GoodShiftFunctorRepresentatives.goodShiftFunctorHomologyIso_image_class (DerivedComparison.supportedSectionsFunctor O ⊤)
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) 2 hF
    (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupSheafMap X C a) n (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (CochainUnit.relativeToSupportedFunctorGlobalSections O) n b)
    (supportedRelativeTwoCupCocycle X C O a n b) rfl

end

/-! The sheaf cup gives exactly the original relative cohomology cup while keeping the test support. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : TopCat.{0}) (C O : Opens X)
variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (C : Set X)) 2)
variable (hF : ∀ n, (HodgeConjecture.DegreeTwo.RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding 2).BoundaryGE n →
  (DerivedComparison.supportedSectionsFunctor O ⊤).PreservesRightHomologyOf
    ((CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C).sc (2+n)))

theorem supportedRelativeTwoCupCocycle_native_class (n : ℕ)
    (b : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) n) :
    HomologicalComplex.homologyMap
      (((DerivedComparison.supportedSectionsFunctor O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X))) (2+n)
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2+n) (supportedRelativeTwoCupCocycle X C O a n b)) =
    HomologicalComplex.homologyMap (CochainUnit.relativeToSupportedFunctorGlobalSections O) (2+n)
      (CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) X (O : Set X) 2 n
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X (C : Set X) 2 (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a))
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n b)) := by
  let d := CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCocycleCupWith X (O : Set X)
    (M := ModuleCat.of ℚ ℚ) (N := ModuleCat.of ℚ ℚ) (L := ModuleCat.of ℚ ℚ)
    (LinearMap.mul ℚ ℚ) 2 n
    (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X (C : Set X)) 2 a) b
  have hd : CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) X (O : Set X) 2 n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X (C : Set X) 2 (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a))
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ n b) = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2+n) d := by
    rw [AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup_class_class]
  let q := ((DerivedComparison.supportedSectionsFunctor O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X))
  calc
    _ = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2+n) (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap q (2+n) (supportedRelativeTwoCupCocycle X C O a n b)) :=
      AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality q (2+n) (supportedRelativeTwoCupCocycle X C O a n b)
    _ = AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2+n) (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (CochainUnit.relativeToSupportedFunctorGlobalSections O) (2+n) d) :=
      congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2+n)) (supportedRelativeTwoCupCocycle_forget X C O a n b)
    _ = HomologicalComplex.homologyMap (CochainUnit.relativeToSupportedFunctorGlobalSections O) (2+n)
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2+n) d) :=
      (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality (CochainUnit.relativeToSupportedFunctorGlobalSections O) (2+n) d).symm
    _ = _ := congrArg (HomologicalComplex.homologyMap (CochainUnit.relativeToSupportedFunctorGlobalSections O) (2+n)) hd.symm

theorem supportedRelativeTwoCup_cohomology (n : ℕ) :
    HomologicalComplex.homologyMap (CochainUnit.relativeToSupportedFunctorGlobalSections O) n ≫
      HomologicalComplex.homologyMap
        (((DerivedComparison.supportedSectionsFunctor O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (HodgeConjecture.DegreeTwo.RelativeCupSheaf.Constructions.relativeTwoCupGoodShiftSheafMap X C a)) n ≫
      (GoodShiftFunctorRepresentatives.goodShiftFunctorHomologyIso (DerivedComparison.supportedSectionsFunctor O ⊤)
        (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSingularSheafComplex (ModuleCat.of ℚ ℚ) X C) 2 hF n).hom ≫
      HomologicalComplex.homologyMap
        (((DerivedComparison.supportedSectionsFunctor O ⊤).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplexInclusion C (HodgeConjecture.DegreeTwo.SingularSheafZeroResolution.Constructions.rationalSingularSheafComplex X))) (2+n) =
    ModuleCat.ofHom (CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup (R := ℚ) X (O : Set X) 2 n
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) X (C : Set X) 2 (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ 2 a))) ≫
      HomologicalComplex.homologyMap (CochainUnit.relativeToSupportedFunctorGlobalSections O) (2+n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  obtain ⟨b, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X (O : Set X)) n b
  simp only [ConcreteCategory.comp_apply]
  rw [supportedRelativeTwoCupCocycle_goodShift_class]
  exact supportedRelativeTwoCupCocycle_native_class X C O a n b

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.CupCocycles
