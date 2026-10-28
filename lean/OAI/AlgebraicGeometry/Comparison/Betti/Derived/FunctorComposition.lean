import OAI.AlgebraicGeometry.Comparison.Betti.Derived.ShiftCoherence

/-! # Functor Composition -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorComposition

noncomputable section

/-! Composition of exact derived functors, normalized on the actual localization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits

universe w₁ w₂ w₃ u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasDerivedCategory.{w₃} E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

def cochainFunctorCompIso :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ G.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)

instance cochainFunctorCompIsoCommShift : NatTrans.CommShift (cochainFunctorCompIso F G).hom ℤ where
  shift_comm n := by
    apply NatTrans.ext
    funext K
    change ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      G.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app K ≫
        ((cochainFunctorCompIso F G).hom.app K)⟦n⟧' =
      (cochainFunctorCompIso F G).hom.app (K⟦n⟧) ≫
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app K
    erw [Functor.commShiftIso_comp_hom_app]
    apply HomologicalComplex.Hom.ext
    funext i
    change (G.map (𝟙 (F.obj (K.X (i + n)))) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp only [G.map_id, Category.id_comp]

def derivedCompositionBeforeLocalization :
    DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      DerivedCategory.Q ⋙ (F ⋙ G).mapDerivedCategory :=
  (Functor.associator DerivedCategory.Q F.mapDerivedCategory G.mapDerivedCategory).symm ≪≫
    isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
    Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q G.mapDerivedCategory ≪≫
    isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ)) G.mapDerivedCategoryFactors ≪≫
    (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (G.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q).symm ≪≫
    isoWhiskerRight (cochainFunctorCompIso F G) DerivedCategory.Q ≪≫
    (F ⋙ G).mapDerivedCategoryFactors.symm

instance derivedCompositionBeforeLocalizationCommShift :
    NatTrans.CommShift (derivedCompositionBeforeLocalization F G).hom ℤ := by
  change NatTrans.CommShift
    ((Functor.associator DerivedCategory.Q F.mapDerivedCategory G.mapDerivedCategory).inv ≫
      Functor.whiskerRight F.mapDerivedCategoryFactors.hom G.mapDerivedCategory ≫
      (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q
        G.mapDerivedCategory).hom ≫
      Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ)) G.mapDerivedCategoryFactors.hom ≫
      (Functor.associator (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (G.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q).inv ≫
      Functor.whiskerRight (cochainFunctorCompIso F G).hom DerivedCategory.Q ≫
      (F ⋙ G).mapDerivedCategoryFactors.inv) ℤ
  infer_instance

def derivedFunctorCompIso :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory :=
  (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (DerivedCategory E)).preimageIso
      (derivedCompositionBeforeLocalization F G)

theorem derivedFunctorCompIso_normalization :
    Functor.whiskerLeft DerivedCategory.Q (derivedFunctorCompIso F G).hom =
      (derivedCompositionBeforeLocalization F G).hom :=
  (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (DerivedCategory E)).map_preimage
      (derivedCompositionBeforeLocalization F G).hom

theorem derivedFunctorCompIso_hom_app (K : CochainComplex C ℤ) :
    (derivedFunctorCompIso F G).hom.app (DerivedCategory.Q.obj K) =
      (derivedCompositionBeforeLocalization F G).hom.app K :=
  congr_app (derivedFunctorCompIso_normalization F G) K

theorem derivedFunctorCompIso_hom_app_explicit (K : CochainComplex C ℤ) :
    (derivedFunctorCompIso F G).hom.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          (F ⋙ G).mapDerivedCategoryFactors.inv.app K := by
  rw [derivedFunctorCompIso_hom_app]
  let Q : CochainComplex E ℤ ⥤ DerivedCategory E := DerivedCategory.Q
  change 𝟙 _ ≫ G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫ 𝟙 _ ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ 𝟙 _ ≫
    Q.map (𝟙 (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
    (F ⋙ G).mapDerivedCategoryFactors.inv.app K = _
  simp only [Category.id_comp]
  erw [Q.map_id, Category.id_comp]

theorem derivedFunctorCompIso_inv_app_explicit (K : CochainComplex C ℤ) :
    (derivedFunctorCompIso F G).inv.app (DerivedCategory.Q.obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  let a := G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app K)
  let b := G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let c := (F ⋙ G).mapDerivedCategoryFactors.app K
  let e := (derivedFunctorCompIso F G).app (DerivedCategory.Q.obj K)
  have h : e.hom = a.hom ≫ b.hom ≫ c.inv := derivedFunctorCompIso_hom_app_explicit F G K
  change e.inv = c.hom ≫ b.inv ≫ a.inv
  have he : e = a ≪≫ b ≪≫ c.symm := Iso.ext h
  exact (congrArg Iso.inv he).trans (Category.assoc c.hom b.inv a.inv)

instance derivedFunctorCompIsoCommShift : NatTrans.CommShift (derivedFunctorCompIso F G).hom ℤ := by
  have : NatTrans.CommShift
      (Functor.whiskerLeft DerivedCategory.Q (derivedFunctorCompIso F G).hom) ℤ := by
    rw [derivedFunctorCompIso_normalization]
    infer_instance
  exact ShiftCoherence.commShift_of_localization
    (DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (derivedFunctorCompIso F G).hom

end

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.FunctorComposition
