import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback

/-! # Open Forms -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.OpenForms

noncomputable section

section

/-! Genuine pullback on the algebraic de Rham hypercohomology construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

def deRhamPresheafPullbackInt : Algebraic.Sheaves.deRhamPresheafOfComplexesInt Y ⟶
    (Opens.map f.left.base).op ⋙ Algebraic.Sheaves.deRhamPresheafOfComplexesInt X :=
  Functor.whiskerRight (Algebraic.Sheaves.deRhamPresheafPullback f)
    ((ComplexShape.embeddingUpIntGE 0).extendFunctor (ModuleCat.{0} ℂ))

def presheafComplexPullbackInt : Algebraic.Sheaves.deRhamPresheafComplexInt Y ⟶
    ((Sheaf.CochainPullback.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (Algebraic.Sheaves.deRhamPresheafComplexInt X) where
  f n :=
    { app := fun U => ((deRhamPresheafPullbackInt f).app U).f n
      naturality := fun _ _ i =>
        congrArg (fun φ => φ.f n) ((deRhamPresheafPullbackInt f).naturality i) }
  comm' i j _ := NatTrans.ext (funext (fun U =>
    ((deRhamPresheafPullbackInt f).app U).comm i j))

def sheafificationComplexAdjunctionInt (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) :
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⊣
      (sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  Complex.Adjunction.onComplexes
    (sheafificationAdjunction (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ))
    (ComplexShape.up ℤ)

def imageComplexAdjunctionInt :
    (Algebraic.Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ) ⊣
      (Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Complex.Adjunction.onComplexes (Algebraic.Sheaves.imageAdjunction f) (ComplexShape.up ℤ)

def presheafToDirectImageSheafComplexInt : Algebraic.Sheaves.deRhamPresheafComplexInt Y ⟶
    ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)) :=
  presheafComplexPullbackInt f ≫
    ((Sheaf.CochainPullback.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((sheafificationComplexAdjunctionInt X).unit.app (Algebraic.Sheaves.deRhamPresheafComplexInt X))

def deRhamSheafDirectImageInt : Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y ⟶
    ((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X) :=
  ((sheafificationComplexAdjunctionInt Y).homEquiv (Algebraic.Sheaves.deRhamPresheafComplexInt Y)
    (((Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X))).symm (presheafToDirectImageSheafComplexInt f)

def deRhamSheafPullbackInt :
    ((Algebraic.Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y) ⟶
      Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X :=
  ((imageComplexAdjunctionInt f).homEquiv (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y)
    (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X)).symm (deRhamSheafDirectImageInt f)

/-- The sheaf-complex pullback passed through the actual localization functor. -/
def derivedDeRhamPullback :
    (Algebraic.Sheaves.derivedInverseImage f).obj (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y)) ⟶
      DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt X) :=
  (Algebraic.Sheaves.inverseImage f).mapDerivedCategoryFactors.hom.app (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y) ≫
    DerivedCategory.Q.map (deRhamSheafPullbackInt f)

def derivedInverseImageConstantIso :
    (Algebraic.Sheaves.derivedInverseImage f).obj
        ((DerivedCategory.singleFunctor (Algebraic.Sheaves.ComplexSheaves Y) 0).obj (Algebraic.Sheaves.constantComplexSheaf Y)) ≅
      (DerivedCategory.singleFunctor (Algebraic.Sheaves.ComplexSheaves X) 0).obj (Algebraic.Sheaves.constantComplexSheaf X) :=
  ((Algebraic.Sheaves.inverseImage f).mapDerivedCategorySingleFunctor 0).app (Algebraic.Sheaves.constantComplexSheaf Y) ≪≫
    (DerivedCategory.singleFunctor (Algebraic.Sheaves.ComplexSheaves X) 0).mapIso (Algebraic.Sheaves.inverseImageConstantIso f)

instance derivedInverseImageCommShift : (Algebraic.Sheaves.derivedInverseImage f).CommShift ℤ :=
  inferInstanceAs ((Algebraic.Sheaves.inverseImage f).mapDerivedCategory.CommShift ℤ)

instance derivedInverseImageAdditive : (Algebraic.Sheaves.derivedInverseImage f).Additive :=
  inferInstanceAs ((Algebraic.Sheaves.inverseImage f).mapDerivedCategory.Additive)

/-- Pullback of algebraic de Rham hypercohomology, constructed from exact
inverse image, the constant-sheaf isomorphism and the pullback of regular forms. -/
def algebraicDeRhamPullback (n : ℕ) : Algebraic.Sheaves.algebraicDeRham Y n ⟶ Algebraic.Sheaves.algebraicDeRham X n :=
  ModuleCat.ofHom
    { toFun := fun α =>
        (derivedInverseImageConstantIso f).inv ≫
          (Algebraic.Sheaves.derivedInverseImage f).map α ≫
          ((Algebraic.Sheaves.derivedInverseImage f).commShiftIso (n : ℤ)).hom.app
            (DerivedCategory.Q.obj (Algebraic.Sheaves.algebraicDeRhamSheafComplexInt Y)) ≫
          (shiftFunctor (DerivedCategory (Algebraic.Sheaves.ComplexSheaves X)) (n : ℤ)).map
            (derivedDeRhamPullback f)
      map_add' := by
        intro α β
        simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
      map_smul' := by
        intro c α
        simp only [Functor.map_smul, Linear.comp_smul, Linear.smul_comp, RingHom.id_apply] }

end

/-! Actual regular-form pullback is invertible on open subsets inside an open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

section

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

def algebraicComplexIso (e : A ≃ₐ[ℂ] B) : Algebraic.Forms.algebraicDeRhamComplex A ≅ Algebraic.Forms.algebraicDeRhamComplex B where
  hom := Algebraic.Forms.complexPullback e.toAlgHom
  inv := Algebraic.Forms.complexPullback e.symm.toAlgHom
  hom_inv_id := by
    rw [← Algebraic.Forms.complexPullback_comp]
    have h : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id ℂ A := by
      ext a
      exact e.symm_apply_apply a
    rw [h, Algebraic.Forms.complexPullback_id]
  inv_hom_id := by
    rw [← Algebraic.Forms.complexPullback_comp]
    have h : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id ℂ B := by
      ext b
      exact e.apply_symm_apply b
    rw [h, Algebraic.Forms.complexPullback_id]

theorem complexPullback_isIso_of_bijective (f : A →ₐ[ℂ] B) (hf : Function.Bijective f) :
    IsIso (Algebraic.Forms.complexPullback f) := (algebraicComplexIso (AlgEquiv.ofBijective f hf)).isIso_hom

end

attribute [local instance] Algebraic.Sheaves.sectionAlgebra

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [IsOpenImmersion f.left]

theorem sectionPullback_bijective_of_openImmersion (U : Y.left.Opens) (hU : U ≤ f.left.opensRange) :
    Function.Bijective (Algebraic.Sheaves.sectionPullback f U) := by
  have : IsIso (f.left.app U) := Scheme.Hom.isIso_app f.left U hU
  change Function.Bijective (f.left.app U)
  exact ConcreteCategory.bijective_of_isIso _

theorem deRhamPresheafPullback_isIso_of_openImmersion (U : Y.left.Opensᵒᵖ)
    (hU : U.unop ≤ f.left.opensRange) : IsIso ((Algebraic.Sheaves.deRhamPresheafPullback f).app U) :=
  complexPullback_isIso_of_bijective (Algebraic.Sheaves.sectionPullback f U.unop)
    (sectionPullback_bijective_of_openImmersion f U.unop hU)

theorem deRhamPresheafPullbackInt_isIso_of_openImmersion (U : Y.left.Opensᵒᵖ)
    (hU : U.unop ≤ f.left.opensRange) : IsIso ((deRhamPresheafPullbackInt f).app U) := by
  have : IsIso ((Algebraic.Sheaves.deRhamPresheafPullback f).app U) :=
    deRhamPresheafPullback_isIso_of_openImmersion f U hU
  change IsIso (((ComplexShape.embeddingUpIntGE 0).extendFunctor (ModuleCat.{0} ℂ)).map
    ((Algebraic.Sheaves.deRhamPresheafPullback f).app U))
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.OpenForms
