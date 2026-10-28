import OAI.NumberTheory.PadicHodge.GeometricComparison.FixedDiagramInverse
import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexDiagonal

/-! # Fixed Frame Diagonal Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FixedFrameDiagonalNaturality.FixedFrameSectionNaturality

noncomputable section

/-! Absolute frame sections, followed by the inverse of local frame
restriction, are natural in compatible fixed and varying frames. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z a b
variable {C : Type u} [Category.{v} C]
  {A : Type w} [Category.{z} A] [Preadditive A]
  {B : Type a} [Category.{b} B] [Preadditive B]
  (S : A ⥤ C ⥤ B) [S.Additive]
  (D D' : C ⥤ CochainComplex B ℕ)
  (P P' : C ⥤ CochainComplex A ℕ)

local instance constPreservesZero : (Functor.const C : B ⥤ C ⥤ B).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable
  (s : D ⋙ (Functor.const C : B ⥤ C ⥤ B).mapHomologicalComplex (.up ℕ) ⟶
    P ⋙ S.mapHomologicalComplex (.up ℕ))
  (s' : D' ⋙ (Functor.const C : B ⥤ C ⥤ B).mapHomologicalComplex (.up ℕ) ⟶
    P' ⋙ S.mapHomologicalComplex (.up ℕ))

def diagonal : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) D ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FixedDiagramTransformation.FixedDiagramSections.target S P) :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (ConstantComplexEvaluated.ConstantComplexDiagonalMap.transformation D
    (P ⋙ S.mapHomologicalComplex (.up ℕ)) s)

theorem diagonal_naturality (d : D ⟶ D') (b : P ⟶ P')
    (h : s ≫ Functor.whiskerRight b (S.mapHomologicalComplex (.up ℕ)) =
      Functor.whiskerRight d ((Functor.const C : B ⥤ C ⥤ B).mapHomologicalComplex (.up ℕ)) ≫ s') :
    diagonal S D P s ≫ FixedDiagramTransformation.FixedDiagramSections.diagonalMap S b =
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) d ≫ diagonal S D' P' s' := by
  have hn := ConstantComplexDiagonal.ConstantComplexDiagonalNaturality.transformation D D'
    (P ⋙ S.mapHomologicalComplex (.up ℕ)) (P' ⋙ S.mapHomologicalComplex (.up ℕ))
    s s' d (Functor.whiskerRight b (S.mapHomologicalComplex (.up ℕ))) h
  exact ((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).map_comp _ _).symm.trans
    ((congrArg (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).map hn).trans
      ((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).map_comp _ _))

theorem fixed_naturality
    {K K' : CochainComplex A ℕ}
    (η : (Functor.const C).obj K ⟶ P) (η' : (Functor.const C).obj K' ⟶ P')
    [IsIso (FixedDiagramTransformation.FixedDiagramSections.map S K P η)] [IsIso (FixedDiagramTransformation.FixedDiagramSections.map S K' P' η')]
    (d : D ⟶ D') (a : K ⟶ K') (b : P ⟶ P')
    (hη : η ≫ b = (Functor.const C).map a ≫ η')
    (hs : s ≫ Functor.whiskerRight b (S.mapHomologicalComplex (.up ℕ)) =
      Functor.whiskerRight d ((Functor.const C : B ⥤ C ⥤ B).mapHomologicalComplex (.up ℕ)) ≫ s') :
    (diagonal S D P s ≫ inv (FixedDiagramTransformation.FixedDiagramSections.map S K P η)) ≫
        (S.mapHomologicalComplex (.up ℕ)).map a =
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) d ≫
        (diagonal S D' P' s' ≫ inv (FixedDiagramTransformation.FixedDiagramSections.map S K' P' η')) :=
  FixedDiagramInverse.FixedDiagramSectionIso.source_naturality S η η' a b
    (diagonal S D P s) (diagonal S D' P' s') (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) d) hη
    (diagonal_naturality S D D' P P' s s' d b hs)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FixedFrameDiagonalNaturality.FixedFrameSectionNaturality
