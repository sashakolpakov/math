import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenPresheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Open.SheafificationComplex
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.PullbackComposition
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De

/-! # Form Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FormRestriction

noncomputable section

section

/-! The original algebraic sheaf-complex pullback is invertible across every open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

abbrev zariskiOpenRestriction : Sheaves.ComplexSheaves Y ⥤ Sheaves.ComplexSheaves X :=
  Open.Image.openRestriction f.left.base f.left.isOpenEmbedding

instance zariskiOpenRestrictionAdditive : (zariskiOpenRestriction f).Additive where
  map_add := by intros; rfl

def zariskiOpenRestrictionAdjunction : zariskiOpenRestriction f ⊣ Sheaves.directImage f :=
  Open.Image.openRestrictionAdjunction f.left.base f.left.isOpenEmbedding

def zariskiOpenRestrictionComplexAdjunction :
    (zariskiOpenRestriction f).mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      (Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Complex.Adjunction.onComplexes (zariskiOpenRestrictionAdjunction f) (ComplexShape.up ℤ)

def zariskiOpenInverseImageComplexIso :
    (Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (zariskiOpenRestriction f).mapHomologicalComplex (ComplexShape.up ℤ) :=
  (OpenForms.imageComplexAdjunctionInt f).leftAdjointUniq (zariskiOpenRestrictionComplexAdjunction f)

def restrictedAlgebraicSheafPullbackInt :
    ((zariskiOpenRestriction f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Sheaves.algebraicDeRhamSheafComplexInt Y) ⟶ Sheaves.algebraicDeRhamSheafComplexInt X :=
  ((zariskiOpenRestrictionComplexAdjunction f).homEquiv (Sheaves.algebraicDeRhamSheafComplexInt Y)
    (Sheaves.algebraicDeRhamSheafComplexInt X)).symm (OpenForms.deRhamSheafDirectImageInt f)

theorem restrictedAlgebraicSheafPullbackInt_isIso : IsIso (restrictedAlgebraicSheafPullbackInt f) := by
  have : IsIso (((Open.SheafificationComplex.openPresheafAdjunctionInt f.left.base f.left.isOpenEmbedding).homEquiv
      (Sheaves.deRhamPresheafComplexInt Y) (Sheaves.deRhamPresheafComplexInt X)).symm (OpenForms.presheafComplexPullbackInt f)) :=
    OpenPresheaf.restrictedAlgebraicPresheafPullbackInt_isIso f
  exact Open.SheafificationComplex.sheafifiedOpenPullbackInt_isIso f.left.base f.left.isOpenEmbedding (OpenForms.presheafComplexPullbackInt f)

theorem deRhamSheafPullbackInt_open_normalization :
    OpenForms.deRhamSheafPullbackInt f =
      (zariskiOpenInverseImageComplexIso f).hom.app (Sheaves.algebraicDeRhamSheafComplexInt Y) ≫
        restrictedAlgebraicSheafPullbackInt f := by
  let a := OpenForms.imageComplexAdjunctionInt f
  let b := zariskiOpenRestrictionComplexAdjunction f
  let P := Sheaves.algebraicDeRhamSheafComplexInt Y
  let Q := Sheaves.algebraicDeRhamSheafComplexInt X
  have hr : b.homEquiv P Q (restrictedAlgebraicSheafPullbackInt f) = OpenForms.deRhamSheafDirectImageInt f :=
    (b.homEquiv P Q).apply_symm_apply _
  have he := AdjunctionComplexUniqueness.leftAdjointUniq_homEquiv a b (restrictedAlgebraicSheafPullbackInt f)
  apply (a.homEquiv P Q).injective
  exact (PullbackComposition.deRhamSheafPullbackInt_normalization f).trans (he.trans hr).symm

theorem deRhamSheafPullbackInt_isIso_of_openImmersion : IsIso (OpenForms.deRhamSheafPullbackInt f) := by
  have : IsIso (restrictedAlgebraicSheafPullbackInt f) := restrictedAlgebraicSheafPullbackInt_isIso f
  rw [deRhamSheafPullbackInt_open_normalization]
  infer_instance

end

/-! The original algebraic form sheaves restrict canonically to actual open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def algebraicFormIntTermIso (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) :
    (Sheaves.algebraicDeRhamSheafComplexInt X).X (n : ℤ) ≅
      (Sheaves.algebraicDeRhamSheafComplex X).X n :=
  (HomologicalComplex.eval _ _ (n : ℤ)).mapIso (Analytic.De.algebraicSheafIntExtensionIso X) ≪≫
    (Sheaves.algebraicDeRhamSheafComplex X).extendXIso (ComplexShape.embeddingUpIntGE 0)
      (by simp)

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

def restrictedAlgebraicSheafComplexIso :
    ((zariskiOpenRestriction f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (Sheaves.algebraicDeRhamSheafComplexInt Y) ≅ Sheaves.algebraicDeRhamSheafComplexInt X := by
  have : IsIso (restrictedAlgebraicSheafPullbackInt f) :=
    restrictedAlgebraicSheafPullbackInt_isIso f
  exact asIso (restrictedAlgebraicSheafPullbackInt f)

def algebraicFormOpenRestrictionIso (n : ℕ) :
    (zariskiOpenRestriction f).obj ((Sheaves.algebraicDeRhamSheafComplex Y).X n) ≅
      (Sheaves.algebraicDeRhamSheafComplex X).X n :=
  (zariskiOpenRestriction f).mapIso (algebraicFormIntTermIso Y n).symm ≪≫
    (HomologicalComplex.eval _ _ (n : ℤ)).mapIso (restrictedAlgebraicSheafComplexIso f) ≪≫
    algebraicFormIntTermIso X n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FormRestriction
