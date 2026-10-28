import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenVector
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction

/-! # Open Zero -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenZero.Constructions

noncomputable section

/-! On an injective coordinate neighborhood the actual diagonal
section vector vanishes precisely on the actual projective diagonal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions.Support OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen
open OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticCoordinateDifference.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem point_mem_diagonal_iff (z : (Ambient.Constructions.productVariety V V).analyticSpace) :
    z ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.diagonal V)) ↔
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.first V V) z = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.second V V) z := by
  constructor
  · rintro ⟨x, rfl⟩
    change (x ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.first V V = (x ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.second V V
    simp only [Category.assoc, Ambient.Constructions.diagonal_first, Ambient.Constructions.diagonal_second]
  · intro h
    refine ⟨z ≫ Ambient.Constructions.first V V, ?_⟩
    apply BinaryFan.IsLimit.hom_ext (Ambient.Constructions.productLimit V V)
    · change ((z ≫ Ambient.Constructions.first V V) ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.first V V = z ≫ Ambient.Constructions.first V V
      rw [Category.assoc, Ambient.Constructions.diagonal_first, Category.comp_id]
    · change ((z ≫ Ambient.Constructions.first V V) ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.second V V = z ≫ Ambient.Constructions.second V V
      rw [Category.assoc, Ambient.Constructions.diagonal_second, Category.comp_id]
      exact h

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)
  [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom] [IsOpenImmersion j.left]

local instance : IsIntegral (X ⊗ X).left := Affine.ProductIs.Constructions.affineProduct_isIntegral X X
local instance : Smooth (X ⊗ X).hom := inferInstanceAs (Smooth (pullback.fst X.hom X.hom ≫ X.hom))
local instance : IsIntegral (Ambient.Constructions.productVariety V V).toOver.left := (Ambient.Constructions.productVariety V V).property
local instance : Smooth (Ambient.Constructions.productVariety V V).toOver.hom := (Ambient.Constructions.productVariety V V).presentation.smooth
local instance : Nonempty (OpenEquations.Constructions.productOpen V X j) :=
  ⟨⟨OpenEquations.Constructions.center V X j (genericPoint X.left), OpenEquations.Constructions.center_mem V X j (genericPoint X.left)⟩⟩

variable (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace)
  (hU : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j)))

theorem lift_first (u : U) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hU u)).1 =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.first V V) u.val := by
  change (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hU u ≫ fst X X) ≫ j = u.val ≫ Ambient.Constructions.first V V
  rw [Category.assoc, ← OpenVector.Constructions.productOpenOverMap_first, ← Category.assoc]
  exact congrArg (fun z => z ≫ Ambient.Constructions.first V V) (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift_commutes (OpenVector.Constructions.productOpenOverMap V X j) U hU u)

theorem lift_second (u : U) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hU u)).2 =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.second V V) u.val := by
  change (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hU u ≫ snd X X) ≫ j = u.val ≫ Ambient.Constructions.second V V
  rw [Category.assoc, ← OpenVector.Constructions.productOpenOverMap_second, ← Category.assoc]
  exact congrArg (fun z => z ≫ Ambient.Constructions.second V V) (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift_commutes (OpenVector.Constructions.productOpenOverMap V X j) U hU u)

variable (hUB : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j))))
  (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  (O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (hi : Set.InjOn (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (EtaleSectionVector.Constructions.coordinateSections X n)) O)
  (hO : ∀ u : U, (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hU u)).1 ∈ O ∧
    (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hU u)).2 ∈ O)

include hi hO in
theorem diagonalBaseVector_zero_iff (u : U) :
    u ∈ Set.range (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularComplementInclusion ↔
      BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j)) U hUB n (OpenEquations.Constructions.diagonalSection V X j n) u = 0 := by
  rw [Closed.ImmersionOpenRestriction.Constructions.Support.restricted_range]
  change u.val ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.diagonal V)) ↔ _
  rw [point_mem_diagonal_iff, OpenVector.Constructions.diagonalBaseVector_apply V X j n U hU hUB]
  change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.first V V) u.val = ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.second V V) u.val ↔
    _ - _ = (0 : Fin n → ℂ)
  rw [sub_eq_zero, ← lift_first V X j U hU u, ← lift_second V X j U hU u]
  constructor
  · intro h
    exact congrArg (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (EtaleSectionVector.Constructions.coordinateSections X n))
      ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j).injective h)
  · intro h
    exact congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) (hi (hO u).1 (hO u).2 h)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenZero.Constructions
