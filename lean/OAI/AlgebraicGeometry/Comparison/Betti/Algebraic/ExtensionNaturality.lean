import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De

/-! # Extension Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.ExtensionNaturality

noncomputable section

/-! The preserved integer-indexed algebraic complex retains its actual pullbacks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- A degree of the sectionwise extension, before sheafification. -/
def algebraicOptionPresheaf (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (o : Option ℕ) : Sheaf.CochainPullback.ComplexPresheaves X where
  obj U := HomologicalComplex.extend.X ((Sheaves.deRhamPresheafOfComplexes X).obj U) o
  map r := HomologicalComplex.extend.mapX ((Sheaves.deRhamPresheafOfComplexes X).map r) o
  map_id U := by
    cases o with
    | none => exact (isZero_zero (ModuleCat.{0} ℂ)).eq_of_src _ _
    | some n => exact congrArg (fun p => p.f n) ((Sheaves.deRhamPresheafOfComplexes X).map_id U)
  map_comp r s := by
    cases o with
    | none => exact (isZero_zero (ModuleCat.{0} ℂ)).eq_of_src _ _
    | some n => exact congrArg (fun p => p.f n) ((Sheaves.deRhamPresheafOfComplexes X).map_comp r s)

def algebraicOptionTransposeIso (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (o : Option ℕ) :
    algebraicOptionPresheaf X o ≅
      HomologicalComplex.extend.X (Complex.Transpose.transpose (Sheaves.deRhamPresheafOfComplexes X)) o :=
  NatIso.ofComponents (fun U => Complex.Transpose.optionXIso (Sheaves.deRhamPresheafOfComplexes X) o U)
    (fun r => Complex.Transpose.optionXIso_naturality (Sheaves.deRhamPresheafOfComplexes X) o r)

def algebraicOptionSheafHom (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (o : Option ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).obj
        (algebraicOptionPresheaf X o) ⟶
      HomologicalComplex.extend.X (Sheaves.algebraicDeRhamSheafComplex X) o :=
  (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).map
      (algebraicOptionTransposeIso X o).hom ≫
    (Complex.Extension.mapXIso
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ))
      (Complex.Transpose.transpose (Sheaves.deRhamPresheafOfComplexes X)) o).hom ≫
    HomologicalComplex.extend.mapX
      (((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (Analytic.De.deRhamPresheafTransposeIso X).hom) o

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

def algebraicOptionPresheafPullback (o : Option ℕ) :
    algebraicOptionPresheaf Y o ⟶ (Sheaf.CochainPullback.directImagePresheaf f).obj (algebraicOptionPresheaf X o) where
  app U := HomologicalComplex.extend.mapX ((Sheaves.deRhamPresheafPullback f).app U) o
  naturality U V r := by
    cases o with
    | none => exact (isZero_zero (ModuleCat.{0} ℂ)).eq_of_src _ _
    | some n => exact congrArg (fun p => p.f n) ((Sheaves.deRhamPresheafPullback f).naturality r)

def algebraicOptionSheafDirectImage (o : Option ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).obj
        (algebraicOptionPresheaf Y o) ⟶
      (Sheaves.directImage f).obj
        ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).obj
          (algebraicOptionPresheaf X o)) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).homEquiv _ _).symm
    (algebraicOptionPresheafPullback f o ≫ (Sheaf.CochainPullback.directImagePresheaf f).map
      ((sheafificationAdjunction (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).unit.app
        (algebraicOptionPresheaf X o)))

theorem algebraicOptionSheafHom_some (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) :
    algebraicOptionSheafHom Z (some n) = 𝟙 ((Sheaves.algebraicDeRhamSheafComplex Z).X n) := by
  have h : (algebraicOptionTransposeIso Z (some n)).hom = 𝟙 (Sheaves.formPresheaf Z n) := by
    apply NatTrans.ext
    funext U
    rfl
  change (presheafToSheaf (Opens.grothendieckTopology Z.left) (ModuleCat.{0} ℂ)).map
      (algebraicOptionTransposeIso Z (some n)).hom ≫ 𝟙 _ ≫
    (presheafToSheaf (Opens.grothendieckTopology Z.left) (ModuleCat.{0} ℂ)).map
      (𝟙 (Sheaves.formPresheaf Z n)) = _
  erw [h, (presheafToSheaf (Opens.grothendieckTopology Z.left) (ModuleCat.{0} ℂ)).map_id]
  erw [Category.id_comp, Category.id_comp]
  rfl

theorem algebraicOptionSheafHom_naturality (o : Option ℕ) :
    algebraicOptionSheafDirectImage f o ≫ (Sheaves.directImage f).map (algebraicOptionSheafHom X o) ≫
      (Complex.Extension.mapXIso (Sheaves.directImage f) (Sheaves.algebraicDeRhamSheafComplex X) o).hom =
    algebraicOptionSheafHom Y o ≫ HomologicalComplex.extend.mapX (Sheaf.CochainPullback.deRhamSheafDirectImage f) o := by
  cases o with
  | none => exact (isZero_zero (Sheaves.ComplexSheaves Y)).eq_of_tgt _ _
  | some n =>
    erw [algebraicOptionSheafHom_some X n, algebraicOptionSheafHom_some Y n,
      (Sheaves.directImage f).map_id]
    change algebraicOptionSheafDirectImage f (some n) ≫ 𝟙 _ ≫ 𝟙 _ =
      𝟙 _ ≫ (Sheaf.CochainPullback.deRhamSheafDirectImage f).f n
    simp only [Category.id_comp, Category.comp_id]
    rfl

theorem algebraicSheafIntExtensionIso_naturality :
    OpenForms.deRhamSheafDirectImageInt f ≫
      ((Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Analytic.De.algebraicSheafIntExtensionIso X).hom ≫
      (Complex.Extension.mapExtendIso (Sheaves.directImage f) (ComplexShape.embeddingUpIntGE 0)
        (Sheaves.algebraicDeRhamSheafComplex X)).hom =
    (Analytic.De.algebraicSheafIntExtensionIso Y).hom ≫
      HomologicalComplex.extendMap (Sheaf.CochainPullback.deRhamSheafDirectImage f) (ComplexShape.embeddingUpIntGE 0) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact algebraicOptionSheafHom_naturality f ((ComplexShape.embeddingUpIntGE 0).r i)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.ExtensionNaturality
