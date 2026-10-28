import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalApp
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi

/-! # Fixed Diagram Transformation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FixedDiagramTransformation.FixedDiagramSections

noncomputable section

/-! A fixed coefficient complex mapping to a varying diagram induces
the original map from its section presheaf to the section diagonal. -/

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

def source : C ⥤ CochainComplex B ℕ :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex.obj
    ((S.mapHomologicalComplex (.up ℕ)).obj K)

def target : C ⥤ CochainComplex B ℕ :=
  BifunctorDiagonalEq.BifunctorDiagonal.functor (Section.ComplexBifunctor.SectionComplexBifunctor.functor S P)

def transformation : source S K ⟶ target S P where
  app X := ((S ⋙ (evaluation C B).obj X).mapHomologicalComplex (.up ℕ)).map (η.app X)
  naturality X Y f := by
    dsimp only [target]
    rw [BifunctorDiagonalEq.BifunctorDiagonal.map_eq]
    apply HomologicalComplex.Hom.ext
    funext q
    have hη : (η.app Y).f q = (η.app X).f q ≫ (P.map f).f q :=
      (Category.id_comp _).symm.trans (congrArg (fun a => a.f q) (η.naturality f))
    have hS := congrArg (fun a => a.app X)
      ((congrArg S.map hη).trans (S.map_comp _ _))
    change (S.obj (K.X q)).map f ≫ (S.map ((η.app Y).f q)).app Y =
      (S.map ((η.app X).f q)).app X ≫
        ((S.map ((P.map f).f q)).app X ≫ (S.obj ((P.obj Y).X q)).map f)
    exact ((S.map ((η.app Y).f q)).naturality f).trans
      ((congrArg (fun a => a ≫ (S.obj ((P.obj Y).X q)).map f) hS).trans (Category.assoc _ _ _))

def sourceIso : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (source S K) ≅
    (S.mapHomologicalComplex (.up ℕ)).obj K := Iso.refl _

def map : (S.mapHomologicalComplex (.up ℕ)).obj K ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (target S P) :=
  (sourceIso S K).inv ≫ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (transformation S K P η)

theorem component (X : C) (q : ℕ) : ((FixedDiagramSections.map S K P η).f q).app X =
    (S.map ((η.app X).f q)).app X := Category.id_comp _

variable {K P} {L : CochainComplex A ℕ} {Q : C ⥤ CochainComplex A ℕ}
  (θ : (Functor.const C).obj L ⟶ Q) (a : K ⟶ L) (b : P ⟶ Q)

def diagonalMap : AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (target S P) ⟶
    AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (target S Q) :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (BifunctorDiagonalApp.BifunctorDiagonalMap.map
    ((flipFunctor _ _ _).map (Functor.whiskerRight b
      (S.mapHomologicalComplex (.up ℕ) ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex))))

theorem naturality
    (h : η ≫ b = (Functor.const C).map a ≫ θ) :
    FixedDiagramSections.map S K P η ≫ diagonalMap S b =
      (S.mapHomologicalComplex (.up ℕ)).map a ≫ FixedDiagramSections.map S L Q θ := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext X
  simp only [HomologicalComplex.comp_f, NatTrans.comp_app, component]
  have hX := congrArg (fun c => (c.app X).f q) h
  change (η.app X).f q ≫ (b.app X).f q = a.f q ≫ (θ.app X).f q at hX
  have hS := congrArg (fun c => (S.map c).app X) hX
  simp only [Functor.map_comp, NatTrans.comp_app] at hS
  exact hS

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FixedDiagramTransformation.FixedDiagramSections
