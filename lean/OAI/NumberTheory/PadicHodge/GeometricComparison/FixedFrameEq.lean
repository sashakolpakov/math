import OAI.NumberTheory.PadicHodge.GeometricComparison.FixedFrameDiagonalNaturality

/-! # Fixed Frame Eq -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FixedFrameEq.FixedFrameSectionReindex

noncomputable section

/-! Restricting both indices of a frame-section diagram commutes with
the diagonal and with the inverse of fixed-frame restriction. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v u' v' w z a b
variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {A : Type w} [Category.{z} A] [Preadditive A]
  {B : Type a} [Category.{b} B] [Preadditive B]
  (F : C' ⥤ C) (S : A ⥤ C ⥤ B) [S.Additive]

abbrev restriction : (C ⥤ B) ⥤ (C' ⥤ B) := (Functor.whiskeringLeft _ _ _).obj F

variable (K : CochainComplex A ℕ) (P : C ⥤ CochainComplex A ℕ)
  (η : (Functor.const C).obj K ⟶ P)

def cone : (Functor.const C').obj K ⟶ F ⋙ P where
  app r := η.app (F.obj r)
  naturality _ _ f := η.naturality (F.map f)

theorem map_eq :
    ((restriction (B := B) F).mapHomologicalComplex (.up ℕ)).map
      (FixedDiagramTransformation.FixedDiagramSections.map S K P η) =
        FixedDiagramTransformation.FixedDiagramSections.map (S ⋙ restriction F) K (F ⋙ P) (cone F K P η) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext r
  change ((FixedDiagramTransformation.FixedDiagramSections.map S K P η).f q).app (F.obj r) = _
  rw [FixedDiagramTransformation.FixedDiagramSections.component, FixedDiagramTransformation.FixedDiagramSections.component]
  rfl

variable (D : C ⥤ CochainComplex B ℕ)

local instance constPreservesZero : (Functor.const C : B ⥤ C ⥤ B).PreservesZeroMorphisms where
  map_zero _ _ := rfl

local instance constPreservesZero' : (Functor.const C' : B ⥤ C' ⥤ B).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable (s : D ⋙ (Functor.const C : B ⥤ C ⥤ B).mapHomologicalComplex (.up ℕ) ⟶
  P ⋙ S.mapHomologicalComplex (.up ℕ))

def transformation : (F ⋙ D) ⋙
    (Functor.const C' : B ⥤ C' ⥤ B).mapHomologicalComplex (.up ℕ) ⟶
      (F ⋙ P) ⋙ (S ⋙ restriction F).mapHomologicalComplex (.up ℕ) where
  app r := ((restriction F).mapHomologicalComplex (.up ℕ)).map (s.app (F.obj r))
  naturality r t f := by
    have h := congrArg (((restriction F).mapHomologicalComplex (.up ℕ)).map)
      (s.naturality (F.map f))
    simp only [Functor.map_comp] at h
    exact h

theorem diagonal_eq :
    ((restriction F).mapHomologicalComplex (.up ℕ)).map
      (FixedFrameDiagonalNaturality.FixedFrameSectionNaturality.diagonal S D P s) =
        FixedFrameDiagonalNaturality.FixedFrameSectionNaturality.diagonal (S ⋙ restriction F) (F ⋙ D) (F ⋙ P)
          (transformation F S P D s) := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext r
  rfl

variable [IsIso (FixedDiagramTransformation.FixedDiagramSections.map S K P η)]

instance reindexed_isIso : IsIso
    (FixedDiagramTransformation.FixedDiagramSections.map (S ⋙ restriction F) K (F ⋙ P) (cone F K P η)) := by
  rw [← map_eq F S K P η]
  infer_instance

theorem fixed_eq :
    ((restriction F).mapHomologicalComplex (.up ℕ)).map
      (FixedFrameDiagonalNaturality.FixedFrameSectionNaturality.diagonal S D P s ≫ inv (FixedDiagramTransformation.FixedDiagramSections.map S K P η)) =
        FixedFrameDiagonalNaturality.FixedFrameSectionNaturality.diagonal (S ⋙ restriction F) (F ⋙ D) (F ⋙ P)
            (transformation F S P D s) ≫
          inv (FixedDiagramTransformation.FixedDiagramSections.map (S ⋙ restriction F) K (F ⋙ P) (cone F K P η)) := by
  simp only [Functor.map_comp, diagonal_eq, Functor.map_inv, map_eq]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FixedFrameEq.FixedFrameSectionReindex
