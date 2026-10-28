import OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtFunctoriality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

/-! # Ext Transport -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtTransport

noncomputable section

/-!
# Coherent transport of Ext with identified coefficient objects

The transport maps use the actual exact functor and object isomorphisms.
Their composition law follows from the checked functoriality of Ext.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe w₁ w₂ w₃

open OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtFunctoriality OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

variable (R : Type*) [CommRing R]
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [Linear R C] [Linear R D] [Linear R E]
  [HasExt.{w₁} C] [HasExt.{w₂} D] [HasExt.{w₃} E]

section Transport

variable (F : C ⥤ D) [F.Additive] [F.Linear R]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Exact-functor transport followed by the specified identifications of both objects. -/
def exactTransport {A B : C} {A' B' : D} (iA : F.obj A ≅ A') (iB : F.obj B ≅ B') (n : ℕ) :
    Ext A B n →ₗ[R] Ext A' B' n :=
  (IntegralComparison.Etale.Frobenius.extIsoCongr R iA iB n).toLinearMap.comp (F.mapExtLinearMap R A B n)

theorem exactTransport_apply {A B : C} {A' B' : D} (iA : F.obj A ≅ A') (iB : F.obj B ≅ B')
    {n : ℕ} (α : Ext A B n) :
    exactTransport R F iA iB n α =
      ((Ext.mk₀ iA.inv).comp (α.mapExactFunctor F) (Nat.zero_add n)).comp
        (Ext.mk₀ iB.hom) (Nat.add_zero n) := rfl

end Transport

section Composition

variable [EnoughInjectives C]
variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.Linear R] [G.Linear R]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

theorem exactTransport_comp {A B : C} {A' B' : D} {A'' B'' : E}
    (iA : F.obj A ≅ A') (iB : F.obj B ≅ B')
    (jA : G.obj A' ≅ A'') (jB : G.obj B' ≅ B'') {n : ℕ} (α : Ext A B n) :
    exactTransport R G jA jB n (exactTransport R F iA iB n α) =
      exactTransport R (F ⋙ G) (G.mapIso iA ≪≫ jA) (G.mapIso iB ≪≫ jB) n α := by
  simp only [exactTransport_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    ExtFunctoriality.mapExactFunctor_compFunctor]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀]
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

end Composition

variable [EnoughInjectives C]
variable {F G : C ⥤ D} [F.Additive] [G.Additive] [F.Linear R] [G.Linear R]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

theorem exactTransport_natIso (e : F ≅ G) {A B : C} {A' B' : D}
    (iA : G.obj A ≅ A') (iB : G.obj B ≅ B') {n : ℕ} (α : Ext A B n) :
    exactTransport R F (e.app A ≪≫ iA) (e.app B ≪≫ iB) n α =
      exactTransport R G iA iB n α := by
  have hn : (Ext.mk₀ (e.inv.app A)).comp
      ((α.mapExactFunctor F).comp (Ext.mk₀ (e.hom.app B)) (Nat.add_zero n)) (Nat.zero_add n) =
        α.mapExactFunctor G := by
    rw [ExtFunctoriality.mapExactFunctor_naturality e.hom α,
      ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    simp only [Iso.inv_hom_id_app, Ext.mk₀_id_comp]
  have hh := congrArg (fun β : Ext (G.obj A) (G.obj B) n =>
    ((Ext.mk₀ iA.inv).comp β (Nat.zero_add n)).comp (Ext.mk₀ iB.hom) (Nat.add_zero n)) hn
  simp only [Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀] at hh
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀] at hh
  simp only [exactTransport_apply, Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom,
    Ext.comp_assoc_of_third_deg_zero]
  exact hh

theorem exactTransport_id {A B : C} {n : ℕ} (α : Ext A B n) :
    exactTransport R (𝟭 C) (Iso.refl A) (Iso.refl B) n α = α := by
  simp only [exactTransport_apply, ExtFunctoriality.mapExactFunctor_id, Iso.refl_inv, Iso.refl_hom,
    Ext.mk₀_id_comp]
  exact Ext.comp_mk₀_id α

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ExtTransport
