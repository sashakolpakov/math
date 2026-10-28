import OAI.AlgebraicGeometry.SheafCohomology.ExtAdjunction
import OAI.AlgebraicGeometry.SheafCohomology.ExtLeft

/-! # Ext Naturality -/

namespace OAI.AlgebraicGeometry.SheafCohomology.ExtNaturality.Projective

noncomputable section

/-! Naturality and additive change of universe for the actual Ext comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe u v w w' u' v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

@[simp] theorem extLeftIso_apply {X Y : C} (e : X ≅ Y) (Z : C) (n : ℕ)
    (x : Ext X Z n) :
    ExtLeft.Projective.extLeftIso e Z n x = (Ext.mk₀ e.inv).comp x (Nat.zero_add n) := rfl

theorem extLeftIso_naturality {X Y Z Z' : C} (e : X ≅ Y) (f : Z ⟶ Z')
    (n : ℕ) (x : Ext X Z n) :
    ExtLeft.Projective.extLeftIso e Z' n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      (ExtLeft.Projective.extLeftIso e Z n x).comp (Ext.mk₀ f) (Nat.add_zero n) := by
  simp only [extLeftIso_apply]
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
variable (G : D ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

theorem extCompare_naturality (X : C) (X₀ : D) (a : X ⟶ G.obj X₀)
    {Y Z : D} (f : Y ⟶ Z) (n : ℕ) (x : Ext X₀ Y n) :
    ExtAdjunction.Projective.extCompare G X X₀ a Z n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      (ExtAdjunction.Projective.extCompare G X X₀ a Y n x).comp (Ext.mk₀ (G.map f)) (Nat.add_zero n) := by
  simp only [ExtAdjunction.Projective.extCompare_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm

/-- Universe resizing respects the abelian-group operation on Ext. -/
def extChangeUniverseAddEquiv [HasExt.{w'} C] (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃+ Ext.{w'} X Y n where
  toEquiv := Ext.chgUniv
  map_add' x y := by
    let := HasDerivedCategory.standard C
    apply Ext.homEquiv.injective
    change Ext.homEquiv (Ext.chgUniv (x + y)) =
      Ext.homEquiv (Ext.chgUniv x + Ext.chgUniv y)
    rw [Ext.homEquiv_chgUniv]
    change (x + y).hom = (Ext.chgUniv x + Ext.chgUniv y).hom
    rw [Ext.add_hom, Ext.add_hom]
    change x.hom + y.hom = Ext.homEquiv (Ext.chgUniv x) + Ext.homEquiv (Ext.chgUniv y)
    rw [Ext.homEquiv_chgUniv, Ext.homEquiv_chgUniv]

theorem extChangeUniverse_comp_mk₀ [HasExt.{w'} C] {X Y Z : C}
    (n : ℕ) (x : Ext.{w} X Y n) (f : Y ⟶ Z) :
    extChangeUniverseAddEquiv.{u, v, w, w'} X Z n (x.comp (Ext.mk₀ f) (Nat.add_zero n)) =
      (extChangeUniverseAddEquiv.{u, v, w, w'} X Y n x).comp (Ext.mk₀ f) (Nat.add_zero n) := by
  let := HasDerivedCategory.standard C
  apply Ext.homEquiv.injective
  simp only [extChangeUniverseAddEquiv, AddEquiv.coe_mk, Ext.homEquiv_chgUniv,
    Ext.comp_hom, Ext.mk₀_hom]

end

end OAI.AlgebraicGeometry.SheafCohomology.ExtNaturality.Projective
