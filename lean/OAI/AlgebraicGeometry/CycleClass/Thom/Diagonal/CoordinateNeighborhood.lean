import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenZero
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct

/-! # Coordinate Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.CoordinateNeighborhood.Constructions

noncomputable section

/-! Genuine product-coordinate neighborhoods around diagonal points,
with both affine lifts in the same injective coordinate domain. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenEquations.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenZero.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.SupportedProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EtaleSectionVector.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.VectorHeadChange.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)
  [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom] [IsOpenImmersion j.left]

local instance : IsIntegral (X ⊗ X).left := Affine.ProductIs.Constructions.affineProduct_isIntegral X X
local instance : Smooth (X ⊗ X).hom := inferInstanceAs (Smooth (pullback.fst X.hom X.hom ≫ X.hom))
local instance : IsIntegral (Ambient.Constructions.productVariety V V).toOver.left := (Ambient.Constructions.productVariety V V).property
local instance : Smooth (Ambient.Constructions.productVariety V V).toOver.hom := (Ambient.Constructions.productVariety V V).presentation.smooth
local instance : Nonempty (OpenEquations.Constructions.productOpen V X j) :=
  ⟨⟨OpenEquations.Constructions.center V X j (genericPoint X.left), OpenEquations.Constructions.center_mem V X j (genericPoint X.left)⟩⟩

def pairEmbedding : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → (Ambient.Constructions.productVariety V V).analyticSpace :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j) ∘ (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X).symm

omit [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom] in
theorem pairEmbedding_open : Topology.IsOpenEmbedding (pairEmbedding V X j) :=
  (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (OpenVector.Constructions.productOpenOverMap V X j)).comp
    (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X).symm.isOpenEmbedding

omit [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom] [IsOpenImmersion j.left] in
theorem pairEmbedding_diagonal (a : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    pairEmbedding V X j (a, a) = SupportedProduct.Constructions.diagonalPointMap V (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j a) := by
  apply BinaryFan.IsLimit.hom_ext (Ambient.Constructions.productLimit V V)
  · change (lift a a ≫ OpenVector.Constructions.productOpenOverMap V X j) ≫ Ambient.Constructions.first V V = (a ≫ j ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.first V V
    rw [Category.assoc, OpenVector.Constructions.productOpenOverMap_first, ← Category.assoc, lift_fst]
    simp only [Category.assoc, Ambient.Constructions.diagonal_first, Category.comp_id]
  · change (lift a a ≫ OpenVector.Constructions.productOpenOverMap V X j) ≫ Ambient.Constructions.second V V = (a ≫ j ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.second V V
    rw [Category.assoc, OpenVector.Constructions.productOpenOverMap_second, ← Category.assoc, lift_snd]
    simp only [Category.assoc, Ambient.Constructions.diagonal_second, Category.comp_id]

def pairOpen (O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) : Opens (Ambient.Constructions.productVariety V V).analyticSpace :=
  ⟨pairEmbedding V X j '' ((O : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) ×ˢ O),
    (pairEmbedding_open V X j).isOpenMap _ (O.isOpen.prod O.isOpen)⟩

omit [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom] in
theorem pairOpen_range (O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :
    (pairOpen V X j O : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j)) := by
  rintro z ⟨ab, _, rfl⟩
  exact ⟨(Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X).symm ab, rfl⟩

omit [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom] in
theorem productOpenPoint_range :
    Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j)) =
      Scheme.SectionEvaluation.Constructions.analyticOpen (Ambient.Constructions.productVariety V V).toOver (OpenEquations.Constructions.productOpen V X j) := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion]
  rfl

theorem pairOpen_lift (O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace)
    (hUO : U ≤ pairOpen V X j O)
    (hUP : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j)))
    (u : U) :
    (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hUP u)).1 ∈ O ∧
      (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hUP u)).2 ∈ O := by
  obtain ⟨ab, hab, he⟩ := hUO u.property
  have hx : IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hUP u = (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X).symm ab :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (OpenVector.Constructions.productOpenOverMap V X j)).injective
      ((IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift_commutes (OpenVector.Constructions.productOpenOverMap V X j) U hUP u).trans he.symm)
  rw [hx, Homeomorph.apply_symm_apply]
  exact hab

variable (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
  [Algebra.FormallyEtale (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]

theorem exists_diagonal_coordinate_neighborhood
    (G : Opens (Ambient.Constructions.productVariety V V).analyticSpace)
    (hGP : (G : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen (Ambient.Constructions.productVariety V V).toOver (OpenEquations.Constructions.productOpen V X j))
    (x : V.analyticSpace) (hx : SupportedProduct.Constructions.diagonalPointMap V x ∈ G) :
    ∃ U : Opens (Ambient.Constructions.productVariety V V).analyticSpace, U ≤ G ∧ SupportedProduct.Constructions.diagonalPointMap V x ∈ U ∧
      ∃ hUP : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j)),
      ∃ _hUB : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion (OpenEquations.Constructions.productOpen V X j))),
      ∃ O : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X),
        Set.InjOn (Section.VectorHeadChange.Constructions.sectionVectorEquation X n (EtaleSectionVector.Constructions.coordinateSections X n)) O ∧
        ∀ u : U, (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hUP u)).1 ∈ O ∧
          (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift (OpenVector.Constructions.productOpenOverMap V X j) U hUP u)).2 ∈ O := by
  have hp : SupportedProduct.Constructions.diagonalPointMap V x ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j)) :=
    (productOpenPoint_range V X j).symm ▸ hGP hx
  obtain ⟨z, hz⟩ := hp
  let a := (Scheme.PointProduct.Constructions.schemePointProductHomeomorph X X z).1
  have ha : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j a = x := by
    have h := congrArg (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Ambient.Constructions.first V V)) hz
    change (z ≫ OpenVector.Constructions.productOpenOverMap V X j) ≫ Ambient.Constructions.first V V = (x ≫ Ambient.Constructions.diagonal V) ≫ Ambient.Constructions.first V V at h
    rw [Category.assoc, OpenVector.Constructions.productOpenOverMap_first, ← Category.assoc, Category.assoc x,
      Ambient.Constructions.diagonal_first, Category.comp_id] at h
    exact h
  obtain ⟨O, haO, hi⟩ := EtaleSectionVector.Constructions.exists_coordinate_injective_neighborhood X n a
  let U := G ⊓ pairOpen V X j O
  have hUP : (U : Set (Ambient.Constructions.productVariety V V).analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (OpenVector.Constructions.productOpenOverMap V X j)) :=
    fun _ hu => pairOpen_range V X j O hu.2
  refine ⟨U, inf_le_left, ⟨hx, ?_⟩, hUP, ?_, O, hi, pairOpen_lift V X j O U inf_le_right hUP⟩
  · exact ⟨(a, a), ⟨haO, haO⟩, (pairEmbedding_diagonal V X j a).trans (congrArg (SupportedProduct.Constructions.diagonalPointMap V) ha)⟩
  · intro u hu
    exact Section.StalkMap.Constructions.VectorGerms.analyticOpen_le_baseRange (Ambient.Constructions.productVariety V V) (OpenEquations.Constructions.productOpen V X j)
      ((productOpenPoint_range V X j) ▸ hUP hu)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.CoordinateNeighborhood.Constructions
