import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveLinearSections
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Category.Preorder

/-! # Limit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Limit

noncomputable section

/-!
# IntegralComparison: compatible bounded sections form the native inverse limit
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveLinearSections

universe u v w z t

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  [Preadditive D] (R : Type t) [CommRing R] [Linear R D]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (M : D) (F : Cᵒᵖ ⥤ D)

def diagram : ℕᵒᵖ ⥤ ModuleCat.{max u z} R where
  obj n := ModuleCat.of R (ExhaustivePresheafSections.Stage P M F n.unop)
  map {n m} α := ModuleCat.ofHom
    { toFun := ExhaustivePresheafSections.restrict P hP M F m.unop n.unop (leOfHom α.unop)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply NatTrans.ext
    funext U
    rfl
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply NatTrans.ext
    funext U
    rfl

def cone : Cone (diagram R P hP M F) where
  pt := ModuleCat.of R (ExhaustiveLinearSections.compatibleSubmodule R P hP M F)
  π :=
    { app := fun n => ModuleCat.ofHom
        { toFun := fun a => a.val n.unop
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      naturality := by
        intro n m α
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact (a.property m.unop n.unop (leOfHom α.unop)).symm }

def lift (s : Cone (diagram R P hP M F)) : s.pt ⟶ (cone R P hP M F).pt :=
  ModuleCat.ofHom
    { toFun := fun x => ⟨fun n => s.π.app (op n) x, by
        intro n m hnm
        exact (congrArg (fun g : s.pt ⟶ (diagram R P hP M F).obj (op n) => g x)
          (s.π.naturality (homOfLE hnm).op)).symm⟩
      map_add' := fun x y => Subtype.ext (funext (fun n => (s.π.app (op n)).hom.map_add x y))
      map_smul' := fun r x => Subtype.ext (funext (fun n => (s.π.app (op n)).hom.map_smul r x)) }

def isLimit : IsLimit (cone R P hP M F) where
  lift := Limit.lift R P hP M F
  fac s n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  uniq s a ha := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    exact congrArg (fun g : s.pt ⟶ (diagram R P hP M F).obj (op n) => g x) (ha (op n))

def limitIso : ModuleCat.of R (ExhaustiveLinearSections.compatibleSubmodule R P hP M F) ≅ limit (diagram R P hP M F) :=
  (Limit.isLimit R P hP M F).conePointUniqueUpToIso (limit.isLimit (diagram R P hP M F))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Limit
