import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.InjectiveRestrictionSections
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Section Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction

noncomputable section

/-!
# IntegralComparison: linear restriction and extension of sections between incoming full subsites
-/

open _root_.CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (M : ModuleCat.{w} R) (P Q : ObjectProperty C) (F : Cᵒᵖ ⥤ ModuleCat.{w} R)

abbrev Sections := (Functor.const P.FullSubcategoryᵒᵖ).obj M ⟶ P.ι.op ⋙ F

def restrict (h : P ≤ Q) : Sections R M Q F →ₗ[R] Sections R M P F where
  toFun a := Functor.whiskerLeft (ObjectProperty.ιOfLE h).op a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restrictGlobal : ((Functor.const Cᵒᵖ).obj M ⟶ F) →ₗ[R] Sections R M P F where
  toFun a := Functor.whiskerLeft P.ι.op a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrict_restrictGlobal (h : P ≤ Q) (a : (Functor.const Cᵒᵖ).obj M ⟶ F) :
    restrict R M P Q F h (restrictGlobal R M Q F a) = restrictGlobal R M P F a := rfl

theorem restrict_refl (a : Sections R M P F) : restrict R M P P F le_rfl a = a := by
  apply NatTrans.ext
  funext U
  rfl

theorem restrict_comp (S : ObjectProperty C) (h : P ≤ Q) (h' : Q ≤ S) (a : Sections R M S F) :
    restrict R M P Q F h (restrict R M Q S F h' a) =
      restrict R M P S F (h.trans h') a := rfl

def map {G : Cᵒᵖ ⥤ ModuleCat.{w} R} (β : F ⟶ G) : Sections R M P F →ₗ[R] Sections R M P G :=
  Linear.rightComp R _ (Functor.whiskerLeft P.ι.op β)

theorem restrict_map {G : Cᵒᵖ ⥤ ModuleCat.{w} R} (β : F ⟶ G) (h : P ≤ Q)
    (a : Sections R M Q F) :
    restrict R M P Q G h (map R M Q F β a) = map R M P F β (restrict R M P Q F h a) := rfl

variable (hP : ∀ {U V : C}, (U ⟶ V) → P V → P U)

include hP in
theorem restrict_surjective [Injective F] (h : P ≤ Q) :
    Function.Surjective (restrict R M P Q F h) := by
  intro a
  obtain ⟨b, hb⟩ := InjectiveSections.restriction_surjective R M P hP F a
  exact ⟨restrictGlobal R M Q F b, hb⟩

include hP in
theorem sheaf_restrict_surjective (T : GrothendieckTopology C)
    [HasSheafify T (ModuleCat.{w} R)] (A : Sheaf T (ModuleCat.{w} R)) [Injective A] (h : P ≤ Q) :
    Function.Surjective (restrict R M P Q A.obj h) := by
  let : Injective A.obj := (sheafToPresheaf T (ModuleCat.{w} R)).injective_obj A
  exact restrict_surjective R M P Q A.obj hP h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionRestriction
