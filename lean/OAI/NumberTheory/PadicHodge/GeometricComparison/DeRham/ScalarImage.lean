import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.Int
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafCoefficientEquivalence
import OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness

/-! # Scalar Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarImage.SectionScalarChange

noncomputable section

section

/-! Canonical comparison between coefficient change and the actual inverse-image functors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)

def restrictMap {X Y : Over (Spec (CommRingCat.of S))} (f : X ⟶ Y) :
    ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X ⟶ ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom Y :=
  (Over.map (Spec.map (CommRingCat.ofHom σ.toRingHom))).map f

abbrev inverseScalars (X : Over (Spec (CommRingCat.of S))) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) ⥤ AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves S X :=
  sheafCompose (Opens.grothendieckTopology X.left) (ModuleCat.restrictScalars σ.symm.toRingHom)

instance inverseScalars_isEquivalence (X : Over (Spec (CommRingCat.of S))) :
    (inverseScalars σ X).IsEquivalence :=
  (SheafCoefficientEquivalence.SheafCoefficients.equivalence (Opens.grothendieckTopology X.left) σ).isEquivalence_inverse

instance inverseScalars_additive (X : Over (Spec (CommRingCat.of S))) :
    (inverseScalars σ X).Additive where
  map_add := by intros; rfl

def coefficientAdjunction (X : Over (Spec (CommRingCat.of S))) :
    SheafScalarChange.SectionScalarChange.sheafRestriction σ X ⊣ inverseScalars σ X :=
  (SheafCoefficientEquivalence.SheafCoefficients.equivalence (Opens.grothendieckTopology X.left) σ).toAdjunction

def coefficientComplexAdjunction (X : Over (Spec (CommRingCat.of S))) :
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapHomologicalComplex (ComplexShape.up ℕ) ⊣
      (inverseScalars σ X).mapHomologicalComplex (ComplexShape.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes (coefficientAdjunction σ X) (ComplexShape.up ℕ)

variable {X Y : Over (Spec (CommRingCat.of S))} (f : X ⟶ Y)

theorem directImage_inverseScalars_commutes :
    inverseScalars σ X ⋙ Int.directImage f =
      Int.directImage (restrictMap σ f) ⋙ inverseScalars σ Y := rfl

def imageScalarIso : Int.inverseImage f ⋙ SheafScalarChange.SectionScalarChange.sheafRestriction σ X ≅
    SheafScalarChange.SectionScalarChange.sheafRestriction σ Y ⋙ Int.inverseImage (restrictMap σ f) :=
  ((Int.imageAdjunction f).comp (coefficientAdjunction σ X)).leftAdjointUniq
    ((coefficientAdjunction σ Y).comp (Int.imageAdjunction (restrictMap σ f)))

def imageScalarComplexIso :
    (Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      (SheafScalarChange.SectionScalarChange.sheafRestriction σ Y).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        (Int.inverseImage (restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ) :=
  ((Int.imageComplexAdjunction f).comp (coefficientComplexAdjunction σ X)).leftAdjointUniq
    ((coefficientComplexAdjunction σ Y).comp (Int.imageComplexAdjunction (restrictMap σ f)))

theorem imageScalarIso_onComplexes (K : CochainComplex (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves S Y) ℕ) :
    (NatTrans.mapHomologicalComplex (imageScalarIso σ f).hom (ComplexShape.up ℕ)).app K =
      (imageScalarComplexIso σ f).hom.app K := by
  have h := AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness.onComplexes_leftAdjointUniq (ComplexShape.up ℕ)
    ((Int.imageAdjunction f).comp (coefficientAdjunction σ X))
    ((coefficientAdjunction σ Y).comp (Int.imageAdjunction (restrictMap σ f))) K
  erw [AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness.onComplexes_comp (ComplexShape.up ℕ)
      (Int.imageAdjunction f) (coefficientAdjunction σ X),
    AlgebraicGeometry.Comparison.Betti.AdjunctionComplexUniqueness.onComplexes_comp (ComplexShape.up ℕ)
      (coefficientAdjunction σ Y) (Int.imageAdjunction (restrictMap σ f))] at h
  exact h.symm

end

/-! Coefficient change commutes with the actual pullback of section forms and their presheaf complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem inverse_square {C : Type*} [Category* C] {A B A' B' : C}
    (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : f ≫ eB.hom = eA.hom ≫ g) : g ≫ eB.inv = eA.inv ≫ f := by
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] using
    congrArg (fun k => eA.inv ≫ k ≫ eB.inv) h.symm

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  {X Y : Over (Spec (CommRingCat.of S))} (f : X ⟶ Y)

theorem formsPullback_square (n : ℕ) :
    Int.formsPullback (restrictMap σ f) n ≫
        (Int.directImagePresheaf (restrictMap σ f)).map (PresheafScalarChange.SectionScalarChange.formsPresheafIso σ X n).hom =
      (PresheafScalarChange.SectionScalarChange.formsPresheafIso σ Y n).hom ≫
        (PresheafScalarChange.SectionScalarChange.presheafRestriction σ Y).map (Int.formsPullback f n) := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  let : Algebra R Γ(Y.left, U.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom Y) U.unop
  let : Algebra S Γ(Y.left, U.unop) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y U.unop
  let : Algebra R Γ(X.left, f.left ⁻¹ᵁ U.unop) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X) (f.left ⁻¹ᵁ U.unop)
  let : Algebra S Γ(X.left, f.left ⁻¹ᵁ U.unop) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S X (f.left ⁻¹ᵁ U.unop)
  exact ScalarFormsChange.FormsScalarChange.formEquiv_naturality
    (A := Γ(Y.left, U.unop)) (B := Γ(X.left, f.left ⁻¹ᵁ U.unop)) σ
    (ScalarFormsChange.SectionScalarChange.sectionBaseMap_comp σ.toRingHom Y U.unop)
    (ScalarFormsChange.SectionScalarChange.sectionBaseMap_comp σ.toRingHom X (f.left ⁻¹ᵁ U.unop))
    (CommAlgCat.ofHom (Int.sectionPullback (restrictMap σ f) U.unop))
    (CommAlgCat.ofHom (Int.sectionPullback f U.unop)) (fun _ => rfl) n ω

theorem presheafPullback_square :
    Int.presheafPullback (restrictMap σ f) ≫
        ((Int.directImagePresheaf (restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (PresheafScalarChange.SectionScalarChange.presheafComplexIso σ X).hom =
      (PresheafScalarChange.SectionScalarChange.presheafComplexIso σ Y).hom ≫
        ((PresheafScalarChange.SectionScalarChange.presheafRestriction σ Y).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (Int.presheafPullback f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact formsPullback_square σ f n

theorem presheafPullback_inverse_square :
    ((PresheafScalarChange.SectionScalarChange.presheafRestriction σ Y).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (Int.presheafPullback f) ≫
      ((Int.directImagePresheaf (restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (PresheafScalarChange.SectionScalarChange.presheafComplexIso σ X).inv =
    (PresheafScalarChange.SectionScalarChange.presheafComplexIso σ Y).inv ≫ Int.presheafPullback (restrictMap σ f) :=
  inverse_square (PresheafScalarChange.SectionScalarChange.presheafComplexIso σ Y)
    (((Int.directImagePresheaf (restrictMap σ f)).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (PresheafScalarChange.SectionScalarChange.presheafComplexIso σ X)) _ _ (presheafPullback_square σ f)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarImage.SectionScalarChange
