import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Ext Functoriality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtFunctoriality.Construction

/-!
# Completion: coherence of exact-functor maps on Ext

Dimension shifting through an injective presentation proves composition and
identity laws without making choices of derived-category comparison maps.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u₁ u₂ u₃ v₁ v₂ v₃ w₁ w₂ w₃

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
    [EnoughInjectives C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
    {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Successive exact-functor maps equal the map for the composite functor. -/
theorem ext_mapExactFunctor_comp {X Y : C} {n : ℕ} (x : Ext X Y n) :
    (x.mapExactFunctor F).mapExactFunctor G = x.mapExactFunctor (F ⋙ G) := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective x
    simp only [Ext.mapExactFunctor_mk₀, Functor.comp_map]
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι Y))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ X hS x
      (Ext.eq_zero_of_injective _) (rfl : n + 1 = n + 1)
    simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ih]

/-- The identity exact functor induces the identity on Ext. -/
theorem ext_mapExactFunctor_id {X Y : C} {n : ℕ} (x : Ext X Y n) :
    x.mapExactFunctor (𝟭 C) = x := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective x
    simp only [Ext.mapExactFunctor_mk₀, Functor.id_map]
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι Y))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ X hS x
      (Ext.eq_zero_of_injective _) (rfl : n + 1 = n + 1)
    simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ih]

variable {F' : C ⥤ D} [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F']

/-- A natural transformation intertwines the maps induced on Ext. -/
theorem ext_mapExactFunctor_naturality (τ : F ⟶ F') {X Y : C} {n : ℕ}
    (x : Ext X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (τ.app Y)) (add_zero n) =
      (Ext.mk₀ (τ.app X)).comp (x.mapExactFunctor F') (zero_add n) := by
  induction n generalizing Y with
  | zero =>
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X Y).surjective x
    simp only [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, τ.naturality]
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι Y))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ X hS x
      (Ext.eq_zero_of_injective _) (rfl : n + 1 = n + 1)
    simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
      Ext.comp_assoc_of_third_deg_zero]
    erw [ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact F)
      (hS.map_of_exact F') (S.mapNatTrans τ)]
    erw [← Ext.comp_assoc_of_second_deg_zero (y.mapExactFunctor F)
      (Ext.mk₀ (τ.app S.X₃)) (hS.map_of_exact F').extClass rfl]
    exact (congrArg (fun z : Ext (F.obj X) (F'.obj S.X₃) n =>
      z.comp (hS.map_of_exact F').extClass rfl) (ih y)).trans
      (Ext.comp_assoc (Ext.mk₀ (τ.app X)) (y.mapExactFunctor F')
        (hS.map_of_exact F').extClass (zero_add n) rfl (by omega))

theorem ext_mapExactFunctor_iso (e : F ≅ F') {X Y : C} {n : ℕ} (x : Ext X Y n) :
    ((Ext.mk₀ (e.inv.app X)).comp (x.mapExactFunctor F) (zero_add n)).comp
        (Ext.mk₀ (e.hom.app Y)) (add_zero n) = x.mapExactFunctor F' := by
  rw [Ext.comp_assoc_of_third_deg_zero, ext_mapExactFunctor_naturality F e.hom,
    Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id_app, Ext.mk₀_id_comp]

variable {F₀₂ : C ⥤ E} [F₀₂.Additive] [PreservesFiniteLimits F₀₂]
    [PreservesFiniteColimits F₀₂]

/-- Composition of Ext transport, including both source and coefficient comparisons. -/
theorem ext_transport_comp (e : F ⋙ G ≅ F₀₂)
    {X Y : C} {S T : D} {U V : E}
    (s : S ⟶ F.obj X) (t : F.obj Y ⟶ T)
    (s' : U ⟶ G.obj S) (t' : G.obj T ⟶ V)
    (s'' : U ⟶ F₀₂.obj X) (t'' : F₀₂.obj Y ⟶ V)
    (hs : s' ≫ G.map s = s'' ≫ e.inv.app X)
    (ht : G.map t ≫ t' = e.hom.app Y ≫ t'')
    {n : ℕ} (x : Ext X Y n) :
    ((Ext.mk₀ s').comp
      ((((Ext.mk₀ s).comp (x.mapExactFunctor F) (zero_add n)).comp
        (Ext.mk₀ t) (add_zero n)).mapExactFunctor G) (zero_add n)).comp
          (Ext.mk₀ t') (add_zero n) =
      ((Ext.mk₀ s'').comp (x.mapExactFunctor F₀₂) (zero_add n)).comp
        (Ext.mk₀ t'') (add_zero n) := by
  calc
    _ = ((Ext.mk₀ s'').comp
        (((Ext.mk₀ (e.inv.app X)).comp (x.mapExactFunctor (F ⋙ G)) (zero_add n)).comp
          (Ext.mk₀ (e.hom.app Y)) (add_zero n)) (zero_add n)).comp
            (Ext.mk₀ t'') (add_zero n) := by
      simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
        ext_mapExactFunctor_comp, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
        Ext.mk₀_comp_mk₀]
      rw [hs, ht]
    _ = _ := by rw [ext_mapExactFunctor_iso (F ⋙ G) e]

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ExtFunctoriality.Construction
