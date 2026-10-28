import OAI.AlgebraicGeometry.Comparison.Betti.ExtExactFunctorNaturality

/-! # Exact Functor Ext Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExactFunctorExtCocycle

noncomputable section

/-! The normalized exact-functor cocycle formula also holds for the
small Ext groups used by native sheaf cohomology. The derived category
and the Ext groups may occupy different universes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe t t' w w' u u' v v'

variable {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{t} C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [HasDerivedCategory.{t'} D] [HasExt.{w'} D]

theorem smallExtMk_hom {X Y : C} (I : InjectiveResolution Y) {n : ℕ}
    (f : X ⟶ I.cocomplex.X n) (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    (I.extMk f (n + 1) rfl hf).hom =
      Comparison.Betti.ResolutionCocycleClass.Ext.resolutionCocycleHom I.ι'
        (f ≫ (I.cochainComplexXIso n n rfl).inv) (by
          rw [I.cochainComplex_d (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by omega)]
          rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hf, zero_comp]) := by
  rw [I.extMk_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    ShiftedHom.comp_mk₀]
  erw [ShiftedHom.mk₀_id_comp, Category.comp_id]
  rfl

theorem smallExt_mapExactFunctor_extMk (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} {Y' : D} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
    (φ : (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (u : F.obj Y ⟶ Y') (h : F.map (I.ι.f 0) ≫ φ.f 0 = u ≫ J.ι.f 0)
    {n : ℕ} (f : X ⟶ I.cocomplex.X n) (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    ((I.extMk f (n + 1) rfl hf).mapExactFunctor F).comp (Ext.mk₀ u) (add_zero n) =
      J.extMk (F.map f ≫ φ.f n) (n + 1) rfl
        (Comparison.Betti.ExtExactFunctorNaturality.resolutionMapCocycle_closed F I J φ f hf) := by
  let f' := f ≫ (I.cochainComplexXIso n n rfl).inv
  have hf' : f' ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0 := by
    rw [I.cochainComplex_d (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by omega)]
    change (f ≫ (I.cochainComplexXIso n n rfl).inv) ≫ _ = _
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hf, zero_comp]
  have hF : F.map f' ≫ ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).d
      (n : ℤ) ((n : ℤ) + 1) = 0 := by
    change F.map f' ≫ F.map (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) = 0
    rw [← F.map_comp, hf', F.map_zero]
  have hp := Comparison.Betti.ResolutionCocycleNaturality.Ext.resolutionCocycleHom_postcomp
    (Comparison.Betti.Derived.ResolutionFunctor.Ext.mappedAugmentation F I.ι') J.ι'
    (Comparison.Betti.ResolutionMapExtension.Ext.extendedResolutionMap F I J φ) u
    (Comparison.Betti.ResolutionMapExtension.Ext.extendedResolutionMap_augmentation F I J φ u h) (F.map f') hF
  apply Ext.ext
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀, Ext.mapExactFunctor_hom]
  erw [smallExtMk_hom I f hf, Comparison.Betti.ResolutionCocycleClass.Ext.resolutionCocycleHom_map F I.ι' f' hf',
    smallExtMk_hom J (F.map f ≫ φ.f n) (Comparison.Betti.ExtExactFunctorNaturality.resolutionMapCocycle_closed F I J φ f hf)]
  refine hp.symm.trans ?_
  congr 1
  exact Comparison.Betti.ResolutionMapExtension.Ext.extendedResolutionMap_cocycle F I J φ n f

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExactFunctorExtCocycle
