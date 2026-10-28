import OAI.NumberTheory.PadicHodge.GeometricComparison.FixedDiagramInverse

/-! # Diagram Section Iso Transfer -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DiagramSectionIsoTransfer.FixedDiagramSectionIsoTransfer

noncomputable section

/-! Isomorphic fixed frames and resolution diagrams transfer the
invertibility of the actual section restriction. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z a b
variable {C : Type u} [Category.{v} C]
  {A : Type w} [Category.{z} A] [Preadditive A]
  {B : Type a} [Category.{b} B] [Preadditive B]
  (S : A ⥤ C ⥤ B) [S.Additive]
  {K L : CochainComplex A ℕ} {P Q : C ⥤ CochainComplex A ℕ}

theorem diagonal_isIso (e : P ≅ Q) : IsIso (FixedDiagramTransformation.FixedDiagramSections.diagonalMap S e.hom) := by
  dsimp only [FixedDiagramTransformation.FixedDiagramSections.diagonalMap, BifunctorDiagonalApp.BifunctorDiagonalMap.map]
  change IsIso ((AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).map _)
  infer_instance

theorem transfer (η : (Functor.const C).obj K ⟶ P)
    (θ : (Functor.const C).obj L ⟶ Q) (a : K ≅ L) (e : P ≅ Q)
    [IsIso (FixedDiagramTransformation.FixedDiagramSections.map S K P η)]
    (h : η ≫ e.hom = (Functor.const C).map a.hom ≫ θ) :
    IsIso (FixedDiagramTransformation.FixedDiagramSections.map S L Q θ) := by
  let : IsIso (FixedDiagramTransformation.FixedDiagramSections.diagonalMap S e.hom) := diagonal_isIso S e
  exact IsIso.of_isIso_fac_left (FixedDiagramTransformation.FixedDiagramSections.naturality S η θ a.hom e.hom h).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DiagramSectionIsoTransfer.FixedDiagramSectionIsoTransfer
