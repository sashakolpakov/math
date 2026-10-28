import OAI.NumberTheory.PadicHodge.GeometricComparison.FixedDiagramTransformation
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Fixed Diagram Inverse -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FixedDiagramInverse.FixedDiagramSectionIso

noncomputable section

/-! Invertible local restrictions identify a section diagonal with
the fixed-frame section complex, naturally in both frames and diagrams. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z a b
variable {C : Type u} [Category.{v} C]
  {A : Type w} [Category.{z} A] [Preadditive A]
  {B : Type a} [Category.{b} B] [Preadditive B]
  (S : A ⥤ C ⥤ B) [S.Additive]
  (K : CochainComplex A ℕ) (P : C ⥤ CochainComplex A ℕ)
  (η : (Functor.const C).obj K ⟶ P)

theorem isIso
    (h : ∀ X, IsIso (((S ⋙ (evaluation C B).obj X).mapHomologicalComplex (.up ℕ)).map (η.app X))) :
    IsIso (FixedDiagramTransformation.FixedDiagramSections.map S K P η) := by
  let (X : C) : IsIso ((FixedDiagramTransformation.FixedDiagramSections.transformation S K P η).app X) := h X
  let : IsIso (FixedDiagramTransformation.FixedDiagramSections.transformation S K P η) := NatIso.isIso_of_isIso_app _
  dsimp only [FixedDiagramTransformation.FixedDiagramSections.map]
  change IsIso ((FixedDiagramTransformation.FixedDiagramSections.sourceIso S K).inv ≫
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ)).map (FixedDiagramTransformation.FixedDiagramSections.transformation S K P η))
  infer_instance

variable {K P} {L : CochainComplex A ℕ} {Q : C ⥤ CochainComplex A ℕ}
  (θ : (Functor.const C).obj L ⟶ Q) (a : K ⟶ L) (b : P ⟶ Q)
  [IsIso (FixedDiagramTransformation.FixedDiagramSections.map S K P η)] [IsIso (FixedDiagramTransformation.FixedDiagramSections.map S L Q θ)]

theorem inverse_naturality (h : η ≫ b = (Functor.const C).map a ≫ θ) :
    inv (FixedDiagramTransformation.FixedDiagramSections.map S K P η) ≫ (S.mapHomologicalComplex (.up ℕ)).map a =
      FixedDiagramTransformation.FixedDiagramSections.diagonalMap S b ≫ inv (FixedDiagramTransformation.FixedDiagramSections.map S L Q θ) :=
  (IntegralComparison.InverseCoordinateHomology.inverse
    (asIso (FixedDiagramTransformation.FixedDiagramSections.map S K P η)) (asIso (FixedDiagramTransformation.FixedDiagramSections.map S L Q θ))
    ((S.mapHomologicalComplex (.up ℕ)).map a) (FixedDiagramTransformation.FixedDiagramSections.diagonalMap S b)
    (FixedDiagramTransformation.FixedDiagramSections.naturality S η θ a b h).symm).symm

theorem source_naturality
    {M N : CochainComplex (C ⥤ B) ℕ}
    (s : M ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FixedDiagramTransformation.FixedDiagramSections.target S P))
    (t : N ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FixedDiagramTransformation.FixedDiagramSections.target S Q))
    (m : M ⟶ N) (h : η ≫ b = (Functor.const C).map a ≫ θ)
    (hs : s ≫ FixedDiagramTransformation.FixedDiagramSections.diagonalMap S b = m ≫ t) :
    (s ≫ inv (FixedDiagramTransformation.FixedDiagramSections.map S K P η)) ≫ (S.mapHomologicalComplex (.up ℕ)).map a =
      m ≫ (t ≫ inv (FixedDiagramTransformation.FixedDiagramSections.map S L Q θ)) := by
  rw [Category.assoc, inverse_naturality S η θ a b h, ← Category.assoc, hs, Category.assoc]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FixedDiagramInverse.FixedDiagramSectionIso
