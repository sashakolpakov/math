import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionMapExtension

/-! # Augmentation Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AugmentationExtension.Complex

noncomputable section

/-! Extend a normalized augmentation square without changing its coefficient map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.Complex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

def augmentationZero {Y : C} {K : CochainComplex C ℕ}
    (a : (CochainComplex.single₀ C).obj Y ⟶ K) : Y ⟶ K.X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 Y).inv ≫ a.f 0

def extendAugmentation {Y : C} {K : CochainComplex C ℕ}
    (a : (CochainComplex.single₀ C).obj Y ⟶ K) :
    (CochainComplex.singleFunctor C 0).obj Y ⟶ K.extend (ComplexShape.embeddingUpIntGE 0) :=
  (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntGE 0) Y 0 0 rfl).inv ≫
    HomologicalComplex.extendMap a (ComplexShape.embeddingUpIntGE 0)

theorem extendAugmentation_f_zero {Y : C} {K : CochainComplex C ℕ}
    (a : (CochainComplex.single₀ C).obj Y ⟶ K) :
    (extendAugmentation a).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).hom ≫ augmentationZero a ≫
        (K.extendXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) rfl).inv := by
  change (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntGE 0) Y 0 0 rfl).inv.f 0 ≫
    (HomologicalComplex.extendMap a (ComplexShape.embeddingUpIntGE 0)).f 0 = _
  erw [HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f a (ComplexShape.embeddingUpIntGE 0) (i := 0) rfl]
  let eS := ((CochainComplex.single₀ C).obj Y).extendXIso
    (ComplexShape.embeddingUpIntGE 0) (i := 0) rfl
  let eN := HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 Y
  let eI := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y
  let eK := K.extendXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) rfl
  change (eI.hom ≫ eN.inv ≫ eS.inv) ≫ eS.hom ≫ a.f 0 ≫ eK.inv =
    eI.hom ≫ (eN.inv ≫ a.f 0) ≫ eK.inv
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

def extendCochainMap (F : C ⥤ D) [F.Additive] {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.extend (ComplexShape.embeddingUpIntGE 0)) ⟶
      L.extend (ComplexShape.embeddingUpIntGE 0) :=
  (Complex.Extension.mapExtendIso F (ComplexShape.embeddingUpIntGE 0) K).hom ≫
    HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntGE 0)

theorem extendCochainMap_f_zero (F : C ⥤ D) [F.Additive]
    {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L) :
    (extendCochainMap F φ).f 0 =
      F.map (K.extendXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) rfl).hom ≫ φ.f 0 ≫
        (L.extendXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) rfl).inv := by
  change (Complex.Extension.mapExtendIso F (ComplexShape.embeddingUpIntGE 0) K).hom.f 0 ≫
    (HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntGE 0)).f 0 = _
  erw [HomologicalComplex.extendMap_f φ (ComplexShape.embeddingUpIntGE 0) (i := 0) rfl,
    ← Category.assoc, ResolutionMapExtension.Complex.mapExtendIso_hom_f]
  rfl

theorem extendAugmentation_square (F : C ⥤ D) [F.Additive]
    {Y : C} {Y' : D} {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (a : (CochainComplex.single₀ C).obj Y ⟶ K)
    (b : (CochainComplex.single₀ D).obj Y' ⟶ L)
    (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L)
    (u : F.obj Y ⟶ Y') (h : F.map (augmentationZero a) ≫ φ.f 0 = u ≫ augmentationZero b) :
    Derived.ResolutionFunctor.Ext.mappedAugmentation F (extendAugmentation a) ≫ extendCochainMap F φ =
      (CochainComplex.singleFunctor D 0).map u ≫ extendAugmentation b := by
  apply HomologicalComplex.from_single_hom_ext
  change (((F.mapCochainComplexSingleFunctor 0).inv.app Y).f 0 ≫
      F.map ((extendAugmentation a).f 0)) ≫ (extendCochainMap F φ).f 0 =
    ((CochainComplex.singleFunctor D 0).map u).f 0 ≫ (extendAugmentation b).f 0
  erw [extendCochainMap_f_zero F φ, extendAugmentation_f_zero a, extendAugmentation_f_zero b,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.single_map_f_self]
  let eY := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y
  let eFY := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj Y)
  let eY' := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y'
  let eK := K.extendXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) rfl
  let eL := L.extendXIso (ComplexShape.embeddingUpIntGE 0) (i := 0) rfl
  let φ₀ : F.obj (K.X 0) ⟶ L.X 0 := φ.f 0
  let a₀ : Y ⟶ K.X 0 := augmentationZero a
  let b₀ : Y' ⟶ L.X 0 := augmentationZero b
  have h₀ : F.map a₀ ≫ φ₀ = u ≫ b₀ := h
  change ((eFY.hom ≫ F.map eY.inv) ≫ F.map (eY.hom ≫ a₀ ≫ eK.inv)) ≫
    (F.map eK.hom ≫ φ₀ ≫ eL.inv) = (eFY.hom ≫ u ≫ eY'.inv) ≫ (eY'.hom ≫ b₀ ≫ eL.inv)
  simp only [F.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (F.map a₀) φ₀, h₀, Category.assoc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.AugmentationExtension.Complex
