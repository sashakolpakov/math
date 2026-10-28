import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleCoordinates
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology

/-! # Point Generator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.PointGenerator

noncomputable section

/-! The original dimension-zero complex generator is represented by the
actual projected point chain, with the native augmentation equal to one. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology.Cycles
open _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def integralRelativePointCycle (X : TopCat.{0}) (A : Set X) (x : X) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) 0 :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) 0
    ⟨CircleArcWinding.integralPointChain X x, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _⟩

def integralRelativePointClass (X : TopCat.{0}) (A : Set X) (x : X) : CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A 0 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) 0 (integralRelativePointCycle X A x)

theorem integralRelativePointClass_projection (X : TopCat.{0}) (A : Set X) (x : X) :
    integralRelativePointClass X A x = homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) 0 (CircleCoordinates.integralPointClass X x) :=
  (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) 0
    ⟨CircleArcWinding.integralPointChain X x, AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _⟩).symm

theorem integralRelativePointClass_map {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (x : X) :
    CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f h 0 (integralRelativePointClass X A x) =
      integralRelativePointClass Y B (f x) := by
  rw [integralRelativePointClass_projection, integralRelativePointClass_projection]
  have hm : homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) 0 ≫ CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f h 0 =
      CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomologyMap f 0 ≫ homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection Y B) 0 := by
    rw [← homologyMap_comp, CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection_naturality, homologyMap_comp]
  exact (ConcreteCategory.congr_hom hm (CircleCoordinates.integralPointClass X x)).trans
    (congrArg (homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection Y B) 0) (CircleCoordinates.integralPointClass_map f x))

theorem integralPointClass_augmentation (X : TopCat.{0}) [PathConnectedSpace X] (x : X) :
    (CycleClass.Geometric.ContractibleModel.Cycles.integralSingularH0Iso X).hom (CircleCoordinates.integralPointClass X x) = 1 := by
  rw [CircleCoordinates.integralPointClass_eq_generator]
  exact ConcreteCategory.congr_hom
    ((TopCat.toSSet.obj X).liftCycles_ιChainComplex_homologyπ_homology₀ε
      (ModuleCat.of ℤ ℤ) ((TopCat.toSSetObj₀Equiv (X := X)).symm x)) 1

theorem integralRelativePointClass_empty_coordinate (X : TopCat.{0}) [PathConnectedSpace X] (x : X) :
    (CycleClass.Geometric.Point.Cycles.relativeEmptyHomologyZeroIso X).hom (integralRelativePointClass X ∅ x) = 1 := by
  rw [integralRelativePointClass_projection]
  change (CycleClass.Geometric.ContractibleModel.Cycles.integralSingularH0Iso X).hom
    ((CycleClass.Geometric.Point.Cycles.relativeEmptyHomologyIso X 0).hom ((CycleClass.Geometric.Point.Cycles.relativeEmptyHomologyIso X 0).inv (CircleCoordinates.integralPointClass X x))) = 1
  rw [Iso.inv_hom_id_apply, integralPointClass_augmentation]

theorem integralRelativePointClass_pointModel_coordinate :
    CycleClass.Geometric.Point.Cycles.pointLocalHomologyZeroIso.hom (integralRelativePointClass CycleClass.Geometric.Point.Cycles.pointModel ({PUnit.unit}ᶜ) PUnit.unit) = 1 := by
  have h : ∀ (A : Set CycleClass.Geometric.Point.Cycles.pointModel) (hA : A = ∅),
      (cast (congrArg (fun U => CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology CycleClass.Geometric.Point.Cycles.pointModel U 0 ≅ ModuleCat.of ℤ ℤ) hA.symm)
        (CycleClass.Geometric.Point.Cycles.relativeEmptyHomologyZeroIso CycleClass.Geometric.Point.Cycles.pointModel)).hom
        (integralRelativePointClass CycleClass.Geometric.Point.Cycles.pointModel A PUnit.unit) = 1 := by
    intro A hA
    subst A
    exact integralRelativePointClass_empty_coordinate CycleClass.Geometric.Point.Cycles.pointModel PUnit.unit
  exact h ({PUnit.unit}ᶜ) CycleClass.Geometric.Point.Cycles.pointModel_punctured_eq_empty

theorem integralRelativePointClass_complexZero_coordinate :
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 0).hom
      (integralRelativePointClass (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ) 0) = 1 := by
  change CycleClass.Geometric.Point.Cycles.pointLocalHomologyZeroIso.hom
    ((CycleClass.Geometric.LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of (Fin 0 → ℂ)) (Y := CycleClass.Geometric.Point.Cycles.pointModel)
      CycleClass.Geometric.Point.Cycles.complexZeroModelHomeomorphPoint 0 0).hom
      (integralRelativePointClass (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ) 0)) = 1
  have hn := integralRelativePointClass_map
    (TopCat.isoOfHomeo (X := TopCat.of (Fin 0 → ℂ)) (Y := CycleClass.Geometric.Point.Cycles.pointModel) CycleClass.Geometric.Point.Cycles.complexZeroModelHomeomorphPoint).hom
    (A := ({0}ᶜ)) (B := ({PUnit.unit}ᶜ))
    (fun x hx => False.elim (hx (Subsingleton.elim _ _))) 0
  change (CycleClass.Geometric.LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of (Fin 0 → ℂ)) (Y := CycleClass.Geometric.Point.Cycles.pointModel)
      CycleClass.Geometric.Point.Cycles.complexZeroModelHomeomorphPoint 0 0).hom
      (integralRelativePointClass (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ) 0) =
    integralRelativePointClass CycleClass.Geometric.Point.Cycles.pointModel ({PUnit.unit}ᶜ) PUnit.unit at hn
  rw [hn]
  exact integralRelativePointClass_pointModel_coordinate

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.PointGenerator
