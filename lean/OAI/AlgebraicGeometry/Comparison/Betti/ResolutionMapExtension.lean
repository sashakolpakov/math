import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension
import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ResolutionFunctor
import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-! # Resolution Map Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ResolutionMapExtension

noncomputable section

/-! Extending the constructed maps of pulled-back resolutions to integer degrees. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Complex
open _root_.Complex

variable {C : Type*} [Category* C] [Abelian C]
  {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

theorem mapXIso_XIso (K : HomologicalComplex C c) {i : Option ι} {j : ι} (h : i = some j) :
    (Complex.Extension.mapXIso F K i).hom ≫ (HomologicalComplex.extend.XIso
      ((F.mapHomologicalComplex c).obj K) h).hom =
      F.map (HomologicalComplex.extend.XIso K h).hom := by
  subst h
  change 𝟙 (F.obj (K.X j)) ≫ 𝟙 (F.obj (K.X j)) = F.map (𝟙 (K.X j))
  rw [Category.id_comp, F.map_id]

theorem mapExtendIso_hom_f (e : c.Embedding c') (K : HomologicalComplex C c)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    ((Complex.Extension.mapExtendIso F e K).hom.f i') ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).hom =
      F.map (K.extendXIso e h).hom :=
  mapXIso_XIso F K (e.r_eq_some h)

end Complex

namespace Ext

variable {C : Type*} [Category* C] [Abelian C]
  {D : Type*} [Category* D] [Abelian D] (F : C ⥤ D) [F.Additive]
  {Y : C} {Y' : D} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
  (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)

def extendedResolutionMap :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex ⟶ J.cochainComplex :=
  (Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat I.cocomplex).hom ≫
    HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat

theorem extendedResolutionMap_f (n : ℕ) :
    (extendedResolutionMap F I J φ).f (n : ℤ) =
      F.map (I.cochainComplexXIso n n rfl).hom ≫ φ.f n ≫ (J.cochainComplexXIso n n rfl).inv := by
  change ((Complex.Extension.mapExtendIso F ComplexShape.embeddingUpNat I.cocomplex).hom.f (n : ℤ)) ≫
    (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat).f (n : ℤ) = _
  erw [HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat (i := n) rfl]
  erw [← Category.assoc, Complex.mapExtendIso_hom_f]
  rfl

theorem extendedResolutionMap_augmentation (u : F.obj Y ⟶ Y')
    (h : F.map (I.ι.f 0) ≫ φ.f 0 = u ≫ J.ι.f 0) :
    Derived.ResolutionFunctor.Ext.mappedAugmentation F I.ι' ≫ extendedResolutionMap F I J φ =
      (CochainComplex.singleFunctor D 0).map u ≫ J.ι' := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    change (((F.mapCochainComplexSingleFunctor 0).inv.app Y).f 0 ≫ F.map (I.ι'.f 0)) ≫
      (extendedResolutionMap F I J φ).f 0 =
        ((CochainComplex.singleFunctor D 0).map u).f 0 ≫ J.ι'.f 0
    erw [extendedResolutionMap_f F I J φ 0, I.ι'_f_zero, J.ι'_f_zero,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self]
    let eY := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y
    let eFY := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj Y)
    let eY' := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y'
    let eI := I.cochainComplexXIso 0 0 rfl
    let eJ := J.cochainComplexXIso 0 0 rfl
    let φ₀ : F.obj (I.cocomplex.X 0) ⟶ J.cocomplex.X 0 := φ.f 0
    let i₀ : Y ⟶ I.cocomplex.X 0 := I.ι.f 0
    let j₀ : Y' ⟶ J.cocomplex.X 0 := J.ι.f 0
    have h₀ : F.map i₀ ≫ φ₀ = u ≫ j₀ := h
    change ((eFY.hom ≫ F.map eY.inv) ≫ F.map (eY.hom ≫ i₀ ≫ eI.inv)) ≫
      (F.map eI.hom ≫ φ₀ ≫ eJ.inv) =
        (eFY.hom ≫ u ≫ eY'.inv) ≫ (eY'.hom ≫ j₀ ≫ eJ.inv)
    simp only [F.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (F.map i₀) φ₀, h₀, Category.assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (F.obj Y) i hi).eq_of_src _ _

theorem extendedResolutionMap_cocycle {X : C} (n : ℕ) (f : X ⟶ I.cocomplex.X n) :
    F.map (f ≫ (I.cochainComplexXIso n n rfl).inv) ≫ (extendedResolutionMap F I J φ).f (n : ℤ) =
      (F.map f ≫ φ.f n) ≫ (J.cochainComplexXIso n n rfl).inv := by
  erw [extendedResolutionMap_f F I J φ n, F.map_comp]
  let eI := I.cochainComplexXIso n n rfl
  let eJ := J.cochainComplexXIso n n rfl
  let φₙ : F.obj (I.cocomplex.X n) ⟶ J.cocomplex.X n := φ.f n
  change (F.map f ≫ F.map eI.inv) ≫ (F.map eI.hom ≫ φₙ ≫ eJ.inv) = (F.map f ≫ φₙ) ≫ eJ.inv
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc]

end Ext

end

end OAI.AlgebraicGeometry.Comparison.Betti.ResolutionMapExtension
