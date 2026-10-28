import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafAdapterNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexExtensionAdapter

/-! # Extension Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ExtensionAdapter.FormsAdapter

noncomputable section

section

/-! Parametric extension of the native sectionwise BettiComparison complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ))

def nativePresheafComplex (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) : CochainComplex (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.ComplexPresheaves X) ℤ :=
  AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transpose
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X ⋙ e.extendFunctor (ModuleCat.{0} ℂ))

def nativeSheafComplex (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) : CochainComplex (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X) ℤ :=
  ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (nativePresheafComplex e X)

def nativePresheafPullback {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    nativePresheafComplex e Y ⟶
      ((AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (nativePresheafComplex e X) :=
  AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transposeMap
    (Functor.whiskerRight (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafPullback f)
      (e.extendFunctor (ModuleCat.{0} ℂ)))

def nativeSheafificationAdjunction (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :=
  AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes
    (sheafificationAdjunction (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ))
    (ComplexShape.up ℤ)

def nativePresheafSheafPullback {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    nativePresheafComplex e Y ⟶
      ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (nativeSheafComplex e X)) :=
  nativePresheafPullback e f ≫
    ((AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.directImagePresheaf f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((nativeSheafificationAdjunction X).unit.app (nativePresheafComplex e X))

def nativeSheafDirectImage {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    nativeSheafComplex e Y ⟶
      ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (nativeSheafComplex e X) :=
  ((nativeSheafificationAdjunction Y).homEquiv (nativePresheafComplex e Y)
    (((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.directImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (nativeSheafComplex e X))).symm (nativePresheafSheafPullback e f)

def nativeSheafPullback {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (nativeSheafComplex e Y) ⟶
      nativeSheafComplex e X :=
  ((AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.imageAdjunction f) (ComplexShape.up ℤ)).homEquiv
    (nativeSheafComplex e Y) (nativeSheafComplex e X)).symm (nativeSheafDirectImage e f)

def nativeExtensionIso (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) : nativeSheafComplex e X ≅
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X).extend e := SheafFormsAdapter.FormsAdapter.sectionSheafExtensionIso X e

theorem nativeSheafPullback_int {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    nativeSheafPullback (ComplexShape.embeddingUpIntGE 0) f = AlgebraicGeometry.Comparison.Betti.OpenForms.deRhamSheafPullbackInt f := rfl

theorem nativePresheafTerm_isZero (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (i : ℤ) (hi : e.r i = none) :
    IsZero ((nativePresheafComplex e X).X i) := by
  apply (Functor.isZero_iff _).mpr
  intro U
  change IsZero (HomologicalComplex.extend.X
    ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X).obj U) (e.r i))
  rw [hi]
  exact isZero_zero _

theorem nativeSheafTerm_isZero (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (i : ℤ) (hi : e.r i = none) :
    IsZero ((nativeSheafComplex e X).X i) :=
  (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).map_isZero
    (nativePresheafTerm_isZero e X i hi)

end

section

/-! Componentwise models of the native extension and its actual pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

section Options
variable {T C : Type*} [Category* T] [Category* C] [Preadditive C] [HasZeroObject C]
  (F : T ⥤ CochainComplex C ℕ)

def optionFunctor (o : Option ℕ) : T ⥤ C where
  obj t := HomologicalComplex.extend.X (F.obj t) o
  map f := HomologicalComplex.extend.mapX (F.map f) o
  map_id t := by
    cases o with
    | none => exact (isZero_zero C).eq_of_src _ _
    | some n => exact congrArg (fun f => f.f n) (F.map_id t)
  map_comp f g := by
    cases o with
    | none => exact (isZero_zero C).eq_of_src _ _
    | some n => exact congrArg (fun f => f.f n) (F.map_comp f g)

def optionFunctorIso (o : Option ℕ) : optionFunctor F o ≅
    HomologicalComplex.extend.X (AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transpose F) o :=
  NatIso.ofComponents (AlgebraicGeometry.Comparison.Betti.Complex.Transpose.optionXIso F o)
    (fun f => AlgebraicGeometry.Comparison.Betti.Complex.Transpose.optionXIso_naturality F o f)

def optionFunctorMap {G : T ⥤ CochainComplex C ℕ} (φ : F ⟶ G) (o : Option ℕ) :
    optionFunctor F o ⟶ optionFunctor G o where
  app t := HomologicalComplex.extend.mapX (φ.app t) o
  naturality t s f := by
    cases o with
    | none => exact (isZero_zero C).eq_of_src _ _
    | some n => exact congrArg (fun f => f.f n) (φ.naturality f)

def optionComplexIso {K L : CochainComplex C ℕ} (e : K ≅ L) (o : Option ℕ) :
    HomologicalComplex.extend.X K o ≅ HomologicalComplex.extend.X L o :=
  match o with
  | some n => (HomologicalComplex.eval C (ComplexShape.up ℕ) n).mapIso e
  | none => Iso.refl _

theorem optionComplexIso_hom {K L : CochainComplex C ℕ} (e : K ≅ L) (o : Option ℕ) :
    (optionComplexIso e o).hom = HomologicalComplex.extend.mapX e.hom o := by
  cases o with
  | none => exact (isZero_zero C).eq_of_src _ _
  | some n => rfl

end Options

theorem map_identity_square {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (X : C) :
    F.map (𝟙 X) ≫ 𝟙 _ ≫ F.map (𝟙 X) = 𝟙 (F.obj X) := by
  simp only [F.map_id, Category.id_comp]

theorem map_identity_action {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    F.map (𝟙 X) ≫ 𝟙 _ ≫ f = f ≫ 𝟙 _ := by
  simp only [F.map_id, Category.id_comp, Category.comp_id]

def optionPresheaf (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (o : Option ℕ) : AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.ComplexPresheaves X :=
  optionFunctor (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X) o

def optionSheaf (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (o : Option ℕ) : AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.ComplexSheaves X :=
  (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).obj (optionPresheaf X o)

def optionPresheafPullback {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (o : Option ℕ) :
    optionPresheaf Y o ⟶ (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.directImagePresheaf f).obj (optionPresheaf X o) :=
  optionFunctorMap _ (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafPullback f) o

def optionSheafDirectImage {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (o : Option ℕ) :
    optionSheaf Y o ⟶ (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.directImage f).obj (optionSheaf X o) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology Y.left) (ModuleCat.{0} ℂ)).homEquiv
    (optionPresheaf Y o) ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.directImage f).obj (optionSheaf X o))).symm
    (optionPresheafPullback f o ≫ (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.directImagePresheaf f).map
      ((sheafificationAdjunction (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).unit.app
        (optionPresheaf X o)))

def optionSheafPullback {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (o : Option ℕ) :
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f).obj (optionSheaf Y o) ⟶ optionSheaf X o :=
  ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.imageAdjunction f).homEquiv (optionSheaf Y o) (optionSheaf X o)).symm
    (optionSheafDirectImage f o)

def optionSheafIso (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (o : Option ℕ) : optionSheaf X o ≅
    HomologicalComplex.extend.X (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) o :=
  (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapIso
      (optionFunctorIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X) o) ≪≫
    AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso
      (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ))
      (AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transpose (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X)) o ≪≫
    optionComplexIso
      (((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).mapIso (SheafFormsAdapter.FormsAdapter.transposeIso X)) o

theorem optionSheafIso_some (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) :
    (optionSheafIso X (some n)).hom = 𝟙 ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X).X n) := by
  change (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).map
      (𝟙 (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.formPresheaf X n)) ≫ 𝟙 _ ≫
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).map
      (𝟙 (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.formPresheaf X n)) = 𝟙 _
  exact map_identity_square
    (presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ))
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.formPresheaf X n)

theorem optionSheafPullback_some {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (n : ℕ) :
    optionSheafPullback f (some n) = (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f).f n := rfl

theorem optionSheafIso_naturality {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (o : Option ℕ) :
    (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f).map (optionSheafIso Y o).hom ≫
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f)
        (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex Y) o).hom ≫
      HomologicalComplex.extend.mapX (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f) o =
    optionSheafPullback f o ≫ (optionSheafIso X o).hom := by
  cases o with
  | none =>
    have h : IsZero (optionSheaf Y none) :=
      (optionSheafIso Y none).isZero_iff.mpr (isZero_zero _)
    exact ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f).map_isZero h).eq_of_src _ _
  | some n =>
    rw [optionSheafIso_some, optionSheafIso_some, optionSheafPullback_some]
    change (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f).map (𝟙 _) ≫ 𝟙 _ ≫
      (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f).f n = (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f).f n ≫ 𝟙 _
    exact map_identity_action (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f) ((AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f).f n)

variable (e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ))

theorem nativeSheafPullback_f {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (i : ℤ) :
    (nativeSheafPullback e f).f i = optionSheafPullback f (e.r i) := rfl

theorem nativeExtensionIso_f (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (i : ℤ) :
    (nativeExtensionIso e X).hom.f i = (optionSheafIso X (e.r i)).hom := by
  let S := presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)
  let I := (S.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso (SheafFormsAdapter.FormsAdapter.transposeIso X)
  change S.map (optionFunctorIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X) (e.r i)).hom ≫
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso S
        (AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transpose (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X)) (e.r i)).hom ≫
      HomologicalComplex.extend.mapX I.hom (e.r i) =
    S.map (optionFunctorIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X) (e.r i)).hom ≫
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso S
        (AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transpose (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X)) (e.r i)).hom ≫
      (optionComplexIso I (e.r i)).hom
  exact congrArg (fun h =>
    S.map (optionFunctorIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X) (e.r i)).hom ≫
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso S
        (AlgebraicGeometry.Comparison.Betti.Complex.Transpose.transpose (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.deRhamPresheafOfComplexes X)) (e.r i)).hom ≫ h)
    (optionComplexIso_hom I (e.r i)).symm

theorem nativeExtensionIso_naturality {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) :
    ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (nativeExtensionIso e Y).hom ≫
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f) e
        (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex Y)).hom ≫
      HomologicalComplex.extendMap (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f) e =
    nativeSheafPullback e f ≫ (nativeExtensionIso e X).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  change (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f).map ((nativeExtensionIso e Y).hom.f i) ≫
    (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f)
      (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex Y) (e.r i)).hom ≫
    HomologicalComplex.extend.mapX (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f) (e.r i) =
      (nativeSheafPullback e f).f i ≫ (nativeExtensionIso e X).hom.f i
  rw [nativeExtensionIso_f, nativeExtensionIso_f, nativeSheafPullback_f]
  exact optionSheafIso_naturality f (e.r i)

end

/-! Native pullback compatibility for the integer-indexed sheaf-complex adapter. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

section Generic
variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  (F : C ⥤ D) [F.Additive]
  (e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ))

def extendedPullback {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (f : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend e) ⟶ L.extend e :=
  (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F e K).hom ≫ HomologicalComplex.extendMap f e

theorem changeEmbedding_pullback {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (f : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L)
    {e' : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)} (h : e = e') :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (SheafFormsAdapter.FormsAdapter.changeEmbeddingIso K h).hom ≫
      extendedPullback F e' f = extendedPullback F e f ≫ (SheafFormsAdapter.FormsAdapter.changeEmbeddingIso L h).hom := by
  subst e'
  simp only [SheafFormsAdapter.FormsAdapter.changeEmbeddingIso, eqToIso.hom, eqToHom_refl,
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map_id, Category.id_comp, Category.comp_id]

theorem extendedPullback_square {K L : CochainComplex C ℕ} {M N : CochainComplex D ℕ}
    (φ : K ⟶ L) (ψ : M ⟶ N)
    (α : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ M)
    (β : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L ⟶ N)
    (h : (F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ ≫ β = α ≫ ψ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (HomologicalComplex.extendMap φ e) ≫
      extendedPullback F e β = extendedPullback F e α ≫ HomologicalComplex.extendMap ψ e := by
  have h₂ := congrArg (fun k => HomologicalComplex.extendMap k e) h
  simp only [HomologicalComplex.extendMap_comp] at h₂
  exact SheafAdapterNaturality.FormsAdapter.composition_square (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso_naturality F e φ) h₂

end Generic

theorem pullback_square_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B C' : C} {X Y Z : D} (a : A ⟶ B) (b : B ⟶ C')
    (x : X ⟶ Y) (y : Y ⟶ Z) (p : F.obj A ⟶ X) (q : F.obj B ⟶ Y) (r : F.obj C' ⟶ Z)
    (h₁ : F.map a ≫ q = p ≫ x) (h₂ : F.map b ≫ r = q ≫ y) :
    F.map (a ≫ b) ≫ r = p ≫ (x ≫ y) := by
  rw [F.map_comp, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y)

theorem sheafIntExtensionIso_naturality :
    ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso Y).hom ≫
      extendedPullback (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f) ComplexShape.embeddingUpNat
        (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f) =
    AlgebraicGeometry.Comparison.Betti.OpenForms.deRhamSheafPullbackInt f ≫ (SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso X).hom :=
  pullback_square_comp ((AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ))
    (nativeExtensionIso (ComplexShape.embeddingUpIntGE 0) Y).hom
    (SheafFormsAdapter.FormsAdapter.changeEmbeddingIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex Y) SheafFormsAdapter.FormsAdapter.embedding_eq).hom
    (nativeExtensionIso (ComplexShape.embeddingUpIntGE 0) X).hom
    (SheafFormsAdapter.FormsAdapter.changeEmbeddingIso (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.algebraicDeRhamSheafComplex X) SheafFormsAdapter.FormsAdapter.embedding_eq).hom
    (AlgebraicGeometry.Comparison.Betti.OpenForms.deRhamSheafPullbackInt f)
    (extendedPullback (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f) (ComplexShape.embeddingUpIntGE 0)
      (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f))
    (extendedPullback (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f) ComplexShape.embeddingUpNat
      (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f))
    (nativeExtensionIso_naturality (ComplexShape.embeddingUpIntGE 0) f)
    (changeEmbedding_pullback (AlgebraicGeometry.Comparison.Betti.Algebraic.Sheaves.inverseImage f) (ComplexShape.embeddingUpIntGE 0)
      (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f) SheafFormsAdapter.FormsAdapter.embedding_eq)

theorem sheafComplexIntIso_naturality :
    ((DeRham.Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso Y).hom ≫ DeRham.Int.sheafPullbackInt f =
      AlgebraicGeometry.Comparison.Betti.OpenForms.deRhamSheafPullbackInt f ≫ (SheafFormsAdapter.FormsAdapter.sheafComplexIntIso X).hom :=
  pullback_square_comp ((DeRham.Int.inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ))
    (SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso Y).hom
    (HomologicalComplex.extendMap (SheafFormsAdapter.FormsAdapter.sheafComplexIso Y).hom ComplexShape.embeddingUpNat)
    (SheafFormsAdapter.FormsAdapter.sheafIntExtensionIso X).hom
    (HomologicalComplex.extendMap (SheafFormsAdapter.FormsAdapter.sheafComplexIso X).hom ComplexShape.embeddingUpNat)
    (AlgebraicGeometry.Comparison.Betti.OpenForms.deRhamSheafPullbackInt f)
    (extendedPullback (DeRham.Int.inverseImage f) ComplexShape.embeddingUpNat (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f))
    (DeRham.Int.sheafPullbackInt f)
    (sheafIntExtensionIso_naturality f)
    (extendedPullback_square (DeRham.Int.inverseImage f) ComplexShape.embeddingUpNat
      (SheafFormsAdapter.FormsAdapter.sheafComplexIso Y).hom (SheafFormsAdapter.FormsAdapter.sheafComplexIso X).hom
      (AlgebraicGeometry.Comparison.Betti.Sheaf.CochainPullback.deRhamSheafPullback f) (DeRham.Int.sheafPullback f) (SheafAdapterNaturality.FormsAdapter.sheafComplexIso_naturality f))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.ExtensionAdapter.FormsAdapter
