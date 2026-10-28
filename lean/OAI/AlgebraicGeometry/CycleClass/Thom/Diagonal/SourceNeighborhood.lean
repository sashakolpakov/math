import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.CoordinateNeighborhood

/-! # Source Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SourceNeighborhood.Constructions

noncomputable section

/-! The coordinate neighborhood of the diagonal can also be chosen
so that its actual source preimage lies in any prescribed source open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped MonoidalCategory TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.CoordinateNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem diagonalPoint_first (x : V.analyticSpace) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.first V V) (SupportedProduct.Constructions.diagonalPointMap V x) = x := by
  change (x ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.first V V = x
  rw [Category.assoc, Ambient.Constructions.diagonal_first, Category.comp_id]

def firstOpen (K : Opens V.analyticSpace) : Opens (Ambient.Constructions.productVariety V V).analyticSpace :=
  ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.first V V) ⁻¹' (K : Set V.analyticSpace),
    K.isOpen.preimage (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Ambient.Constructions.first V V))⟩

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)
  [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom] [IsOpenImmersion j.left]
  (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [Algebra.FormallyEtale (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

local instance : IsIntegral (X ⊗ X).left := Affine.ProductIs.Constructions.affineProduct_isIntegral X X
local instance : Smooth (X ⊗ X).hom := inferInstanceAs (Smooth (pullback.fst X.hom X.hom ≫ X.hom))
local instance : IsIntegral (Ambient.Constructions.productVariety V V).toOver.left := (Ambient.Constructions.productVariety V V).property
local instance : Smooth (Ambient.Constructions.productVariety V V).toOver.hom := (Ambient.Constructions.productVariety V V).presentation.smooth
local instance : Nonempty (OpenEquations.Constructions.productOpen V X j) :=
  ⟨⟨OpenEquations.Constructions.center V X j (genericPoint X.left), OpenEquations.Constructions.center_mem V X j (genericPoint X.left)⟩⟩

theorem exists_diagonal_source_neighborhood
    (G : Opens (Ambient.Constructions.productVariety V V).analyticSpace)
    (hGP : (G : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen (Ambient.Constructions.productVariety V V).toOver (OpenEquations.Constructions.productOpen V X j))
    (K : Opens V.analyticSpace) (x : V.analyticSpace) (hxG : SupportedProduct.Constructions.diagonalPointMap V x ∈ G) (hxK : x ∈ K) :
    ∃ U : Opens (Ambient.Constructions.productVariety V V).analyticSpace, U ≤ G ∧ SupportedProduct.Constructions.diagonalPointMap V x ∈ U ∧
      Closed.ImmersionOpenRestriction.Constructions.sourceOpen (ComplexImmersion.Constructions.diagonalImmersion V) U ≤ K ∧
      ∃ hUP : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j)),
      ∃ _hUB : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j))),
      ∃ O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X),
        Set.InjOn (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (EtaleSectionVector.Constructions.coordinateSections X n)) O ∧
        ∀ u : U, (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hUP u)).1 ∈ O ∧
          (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hUP u)).2 ∈ O := by
  have hx : SupportedProduct.Constructions.diagonalPointMap V x ∈ G ⊓ firstOpen V K :=
    ⟨hxG, by change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.first V V) (SupportedProduct.Constructions.diagonalPointMap V x) ∈ K; rw [diagonalPoint_first]; exact hxK⟩
  obtain ⟨U, hUG, hxU, hUP, hUB, O, hi, hO⟩ := CoordinateNeighborhood.Constructions.exists_diagonal_coordinate_neighborhood V X j n
    (G ⊓ firstOpen V K) (fun _ h => hGP h.1) x hx
  refine ⟨U, hUG.trans inf_le_left, hxU, ?_, hUP, hUB, O, hi, hO⟩
  intro y hy
  have h : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.first V V) (SupportedProduct.Constructions.diagonalPointMap V y) ∈ K := (hUG hy).2
  rwa [diagonalPoint_first] at h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SourceNeighborhood.Constructions
