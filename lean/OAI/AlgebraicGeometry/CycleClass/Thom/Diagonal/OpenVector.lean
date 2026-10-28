import OAI.AlgebraicGeometry.CycleClass.Thom.Open.RangeOver
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEvaluation

/-! # Open Vector -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenVector.Constructions

noncomputable section

/-! The section vector on the literal open of the projective product
is the actual coordinate difference on its affine product source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.RangeOver.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DiagonalEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticCoordinateDifference.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)

def productOpenOverMap : X ⊗ X ⟶ (Ambient.Constructions.productVariety V V).toOver :=
  Over.homMk (OpenNeighborhood.Constructions.productOpenMap V X j) (by
    change OpenNeighborhood.Constructions.productOpenMap V X j ≫ (pullback.fst V.structureMap V.structureMap ≫ V.structureMap) =
      pullback.fst X.hom X.hom ≫ X.hom
    have hf : OpenNeighborhood.Constructions.productOpenMap V X j ≫ pullback.fst V.structureMap V.structureMap = pullback.fst X.hom X.hom ≫ j.left :=
      pullback.lift_fst _ _ _
    rw [← Category.assoc, hf, Category.assoc]
    exact congrArg (fun f : X.left ⟶ Foundations.Scheme.ProjectiveSpace.complexBase => pullback.fst X.hom X.hom ≫ f) j.w)

instance productOpenOverMap_open [IsOpenImmersion j.left] : IsOpenImmersion (productOpenOverMap V X j).left :=
  OpenNeighborhood.Constructions.productOpenMap_open V X j

@[reassoc]
theorem productOpenOverMap_first : productOpenOverMap V X j ≫ Ambient.Constructions.first V V = fst X X ≫ j := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem productOpenOverMap_second : productOpenOverMap V X j ≫ Ambient.Constructions.second V V = snd X X ≫ j := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

variable [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom] [IsOpenImmersion j.left]

local instance : IsIntegral (X ⊗ X).left := Affine.ProductIs.Constructions.affineProduct_isIntegral X X
local instance : Smooth (X ⊗ X).hom := inferInstanceAs (Smooth (pullback.fst X.hom X.hom ≫ X.hom))
local instance : IsIntegral (Ambient.Constructions.productVariety V V).toOver.left := (Ambient.Constructions.productVariety V V).property
local instance : Smooth (Ambient.Constructions.productVariety V V).toOver.hom := (Ambient.Constructions.productVariety V V).presentation.smooth
local instance : Nonempty (OpenEquations.Constructions.productOpen V X j) :=
  ⟨⟨OpenEquations.Constructions.center V X j (genericPoint X.left), OpenEquations.Constructions.center_mem V X j (genericPoint X.left)⟩⟩

variable (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

omit [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] in
theorem diagonalBaseVector_eq (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace)
    (hU : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (productOpenOverMap V X j)))
    (hUB : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)))) :
    BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB n (OpenEquations.Constructions.diagonalSection V X j n) =
      IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (productOpenOverMap V X j) U hU ≫ Affine.DiagonalEvaluation.Constructions.diagonalVector X n :=
  Open.RangeOver.Constructions.rangeBaseSectionVector (productOpenOverMap V X j) U hU hUB n (Affine.DiagonalEquations.Constructions.coordinateDifferenceSection X n)

theorem diagonalBaseVector_apply (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace)
    (hU : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (productOpenOverMap V X j)))
    (hUB : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)))) (u : U) :
    BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB n (OpenEquations.Constructions.diagonalSection V X j n) u =
      AnalyticCoordinateDifference.Constructions.coordinateDifference n (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (EtaleSectionVector.Constructions.coordinateSections X n))
        (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (productOpenOverMap V X j) U hU u)) := by
  rw [diagonalBaseVector_eq]
  exact congrFun (Affine.DiagonalEvaluation.Constructions.diagonalVector_eq_difference X n) (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (productOpenOverMap V X j) U hU u)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenVector.Constructions
