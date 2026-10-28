import OAI.AlgebraicGeometry.Comparison.Betti.ExtCocycleNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionCocycleNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionMapExtension

/-! # Ext Exact Functor Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExtExactFunctorNaturality

noncomputable section

/-! Exact functors act on Ext through the constructed normalized resolution maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe w w' u u' v v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} {Y' : D} (I : InjectiveResolution Y) (J : InjectiveResolution Y')
  (φ : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)

omit [HasDerivedCategory C] [HasExt C] [HasDerivedCategory D] [HasExt D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
theorem resolutionMapCocycle_closed {n : ℕ} (f : X ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    (F.map f ≫ φ.f n) ≫ J.cocomplex.d n (n + 1) = 0 := by
  erw [Category.assoc, φ.comm n (n + 1), ← Category.assoc]
  change (F.map f ≫ F.map (I.cocomplex.d n (n + 1))) ≫ φ.f (n + 1) = 0
  erw [← F.map_comp, hf, F.map_zero, zero_comp]

theorem mapExactFunctor_extMk (u : F.obj Y ⟶ Y')
    (h : F.map (I.ι.f 0) ≫ φ.f 0 = u ≫ J.ι.f 0)
    {n : ℕ} (f : X ⟶ I.cocomplex.X n) (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    ((I.extMk f (n + 1) rfl hf).mapExactFunctor F).comp (Ext.mk₀ u) (add_zero n) =
      J.extMk (F.map f ≫ φ.f n) (n + 1) rfl (resolutionMapCocycle_closed F I J φ f hf) := by
  let f' := f ≫ (I.cochainComplexXIso n n rfl).inv
  have hf' : f' ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0 := by
    rw [I.cochainComplex_d (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by omega)]
    change (f ≫ (I.cochainComplexXIso n n rfl).inv) ≫ _ = _
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hf, zero_comp]
  have hF : F.map f' ≫ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).d
      (n : ℤ) ((n : ℤ) + 1) = 0 := by
    change F.map f' ≫ F.map (I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1)) = 0
    rw [← F.map_comp, hf', F.map_zero]
  have hp := ResolutionCocycleNaturality.Ext.resolutionCocycleHom_postcomp (Derived.ResolutionFunctor.Ext.mappedAugmentation F I.ι') J.ι'
    (ResolutionMapExtension.Ext.extendedResolutionMap F I J φ) u (ResolutionMapExtension.Ext.extendedResolutionMap_augmentation F I J φ u h)
      (F.map f') hF
  apply Ext.ext
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀, Ext.mapExactFunctor_hom]
  erw [ExtCocycleNormalization.extMk_hom_resolutionCocycleHom I f hf, ResolutionCocycleClass.Ext.resolutionCocycleHom_map F I.ι' f' hf',
    ExtCocycleNormalization.extMk_hom_resolutionCocycleHom J (F.map f ≫ φ.f n) (resolutionMapCocycle_closed F I J φ f hf)]
  refine hp.symm.trans ?_
  congr 1
  exact ResolutionMapExtension.Ext.extendedResolutionMap_cocycle F I J φ n f

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExtExactFunctorNaturality
