import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction

/-! # Cochain Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback

noncomputable section

/-! Construction of pullback on algebraic de Rham sheaf complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

abbrev ComplexPresheaves (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) := X.left.Opensᵒᵖ ⥤ ModuleCat.{0} ℂ

def directImagePresheaf : ComplexPresheaves X ⥤ ComplexPresheaves Y :=
  (Functor.whiskeringLeft _ _ _).obj (Opens.map f.left.base).op

instance directImagePresheafAdditive : (directImagePresheaf f).Additive :=
  inferInstanceAs (((Functor.whiskeringLeft _ _ _).obj (Opens.map f.left.base).op).Additive)

instance directImageIsRightAdjoint : (Algebraic.Sheaves.directImage f).IsRightAdjoint :=
  (Algebraic.Sheaves.imageAdjunction f).isRightAdjoint

instance directImageAdditive : (Algebraic.Sheaves.directImage f).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (Algebraic.Sheaves.directImage f)
  exact (Algebraic.Sheaves.directImage f).additive_of_preservesBinaryBiproducts

def presheafComplexPullback : Algebraic.Sheaves.deRhamPresheafComplex Y ⟶
    ((directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Algebraic.Sheaves.deRhamPresheafComplex X) :=
  CochainComplex.ofHom
    (fun n =>
      { app := fun U => ((Algebraic.Sheaves.deRhamPresheafPullback f).app U).f n
        naturality := fun U V i =>
          congrArg (fun φ => φ.f n) ((Algebraic.Sheaves.deRhamPresheafPullback f).naturality i) })
    (fun n => by
      change _ ≫ (directImagePresheaf f).map ((Algebraic.Sheaves.deRhamPresheafComplex X).d n (n + 1)) =
        (Algebraic.Sheaves.deRhamPresheafComplex Y).d n (n + 1) ≫ _
      rw [Algebraic.Sheaves.deRhamPresheafComplex_d, Algebraic.Sheaves.deRhamPresheafComplex_d]
      apply NatTrans.ext
      funext U
      exact ((Algebraic.Sheaves.deRhamPresheafPullback f).app U).comm n (n + 1))

def sheafificationComplexAdjunction (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ) ⊣
      (sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ) :=
  Complex.Adjunction.onComplexes
    (sheafificationAdjunction (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ))
    (ComplexShape.up ℕ)

def imageComplexAdjunction :
    (Algebraic.Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ) ⊣
      (Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℕ) :=
  Complex.Adjunction.onComplexes (Algebraic.Sheaves.imageAdjunction f) (ComplexShape.up ℕ)

/-- Compose the genuine presheaf pullback with the sheafification unit. -/
def presheafToDirectImageSheafComplex : Algebraic.Sheaves.deRhamPresheafComplex Y ⟶
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Algebraic.Sheaves.algebraicDeRhamSheafComplex X)) :=
  presheafComplexPullback f ≫
    ((directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((sheafificationComplexAdjunction X).unit.app (Algebraic.Sheaves.deRhamPresheafComplex X))

/-- The universal property of sheafification descends the presheaf map. -/
def deRhamSheafDirectImage : Algebraic.Sheaves.algebraicDeRhamSheafComplex Y ⟶
    ((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Algebraic.Sheaves.algebraicDeRhamSheafComplex X) :=
  ((sheafificationComplexAdjunction Y).homEquiv (Algebraic.Sheaves.deRhamPresheafComplex Y)
    (((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Algebraic.Sheaves.algebraicDeRhamSheafComplex X))).symm (presheafToDirectImageSheafComplex f)

/-- Pullback of the algebraic de Rham complex as a morphism of sheaf complexes. -/
def deRhamSheafPullback :
    ((Algebraic.Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Algebraic.Sheaves.algebraicDeRhamSheafComplex Y) ⟶
      Algebraic.Sheaves.algebraicDeRhamSheafComplex X :=
  ((imageComplexAdjunction f).homEquiv (Algebraic.Sheaves.algebraicDeRhamSheafComplex Y)
    (Algebraic.Sheaves.algebraicDeRhamSheafComplex X)).symm (deRhamSheafDirectImage f)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback
