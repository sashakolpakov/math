import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionCocycleClass

/-! # Resolution Cocycle Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ResolutionCocycleNaturality.Ext

noncomputable section

/-! Actual normalized maps of resolutions preserve their derived cocycle classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CochainComplex.HomComplex

universe w u v

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {X Y Y' : C} {K L : CochainComplex C ℤ} {n : ℤ}

omit [HasDerivedCategory C] in
theorem singleCocycleHom_postcomp (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0)
    (g : K ⟶ L) :
    SingleCocycleFunctor.Ext.singleCocycleHom (f ≫ g.f n)
        (by rw [Category.assoc, g.comm, ← Category.assoc, hf, zero_comp]) =
      SingleCocycleFunctor.Ext.singleCocycleHom f hf ≫ g⟦n⟧' :=
  (congrArg Cocycle.equivHomShift.symm
    (Cocycle.fromSingleMk_postcomp f (zero_add n) (n + 1) rfl hf g)).trans
      (Cocycle.equivHomShift_symm_postcomp _ g)

theorem resolutionCocycleHom_postcomp
    (a : (CochainComplex.singleFunctor C 0).obj Y ⟶ K) [QuasiIso a]
    (b : (CochainComplex.singleFunctor C 0).obj Y' ⟶ L) [QuasiIso b]
    (g : K ⟶ L) (u : Y ⟶ Y') (h : a ≫ g = (CochainComplex.singleFunctor C 0).map u ≫ b)
    (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    ResolutionCocycleClass.Ext.resolutionCocycleHom b (f ≫ g.f n)
        (by rw [Category.assoc, g.comm, ← Category.assoc, hf, zero_comp]) =
      ResolutionCocycleClass.Ext.resolutionCocycleHom a f hf ≫ ((DerivedCategory.singleFunctor C 0).map u)⟦n⟧' := by
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  have ha : IsIso (Q.map a) := (DerivedCategory.isIso_Q_map_iff_quasiIso C a).mpr inferInstance
  have hb : IsIso (Q.map b) := (DerivedCategory.isIso_Q_map_iff_quasiIso C b).mpr inferInstance
  have hq : Q.map g ≫ inv (Q.map b) = inv (Q.map a) ≫
      (DerivedCategory.singleFunctor C 0).map u := by
    apply (cancel_epi (Q.map a)).mp
    erw [← Category.assoc, ← Q.map_comp, h, Q.map_comp, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rfl
  let c := SingleCocycleFunctor.Ext.singleCocycleHom f hf
  have hm : ShiftedHom.map (c ≫ g⟦n⟧') Q =
      ShiftedHom.map c Q ≫ (Q.map g)⟦n⟧' := by
    have h' := ShiftedHom.map_comp c (ShiftedHom.mk₀ (0 : ℤ) rfl g) (zero_add n) Q
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] using h'
  change ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom (f ≫ g.f n) _) Q ≫ (inv (Q.map b))⟦n⟧' =
    (ShiftedHom.map c Q ≫ (inv (Q.map a))⟦n⟧') ≫
      ((DerivedCategory.singleFunctor C 0).map u)⟦n⟧'
  erw [singleCocycleHom_postcomp f hf g, hm, Category.assoc, ← Functor.map_comp, hq, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

omit [HasDerivedCategory C] in
theorem singleCocycleHom_precomp {X' : C} (v : X' ⟶ X)
    (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    SingleCocycleFunctor.Ext.singleCocycleHom (v ≫ f) (by rw [Category.assoc, hf, comp_zero]) =
      (CochainComplex.singleFunctor C 0).map v ≫ SingleCocycleFunctor.Ext.singleCocycleHom f hf :=
  (congrArg Cocycle.equivHomShift.symm
    (Cocycle.fromSingleMk_precomp v f (zero_add n) (n + 1) rfl hf)).trans
      (Cocycle.equivHomShift_symm_precomp _ _)

theorem resolutionCocycleHom_precomp
    (a : (CochainComplex.singleFunctor C 0).obj Y ⟶ K) [QuasiIso a]
    {X' : C} (v : X' ⟶ X) (f : X ⟶ K.X n) (hf : f ≫ K.d n (n + 1) = 0) :
    ResolutionCocycleClass.Ext.resolutionCocycleHom a (v ≫ f) (by rw [Category.assoc, hf, comp_zero]) =
      (DerivedCategory.singleFunctor C 0).map v ≫ ResolutionCocycleClass.Ext.resolutionCocycleHom a f hf := by
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  have ha : IsIso (Q.map a) := (DerivedCategory.isIso_Q_map_iff_quasiIso C a).mpr inferInstance
  change ShiftedHom.map (SingleCocycleFunctor.Ext.singleCocycleHom (v ≫ f) _) Q ≫ (inv (Q.map a))⟦n⟧' = _
  erw [singleCocycleHom_precomp v f hf]
  dsimp only [ShiftedHom.map]
  erw [Q.map_comp ((CochainComplex.singleFunctor C 0).map v) (SingleCocycleFunctor.Ext.singleCocycleHom f hf)]
  change (((DerivedCategory.singleFunctor C 0).map v ≫
      Q.map (SingleCocycleFunctor.Ext.singleCocycleHom f hf)) ≫ (Q.commShiftIso n).hom.app K) ≫ (inv (Q.map a))⟦n⟧' = _
  erw [Category.assoc ((DerivedCategory.singleFunctor C 0).map v)
    (Q.map (SingleCocycleFunctor.Ext.singleCocycleHom f hf)) ((Q.commShiftIso n).hom.app K)]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.Comparison.Betti.ResolutionCocycleNaturality.Ext
