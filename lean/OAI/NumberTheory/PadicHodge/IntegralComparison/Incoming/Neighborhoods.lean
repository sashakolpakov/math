import Mathlib

/-! # Neighborhoods -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Neighborhoods

noncomputable section

/-!
# IntegralComparison: filtered neighborhoods underlying the inverse image of incoming-section presheaves
-/

open _root_.CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] {A : Type w} [SemilatticeInf A] [OrderTop A]
  (P : A → ObjectProperty C)

def property (T : C) : ObjectProperty A := fun V => P V T

abbrev Objects (T : C) := (Neighborhoods.property P T).FullSubcategory

def inclusion (T : C) : Objects P T ⥤ A := (Neighborhoods.property P T).ι

variable (hTop : ∀ T, P ⊤ T) (hInf : ∀ U V T, P U T → P V T → P (U ⊓ V) T)

include hTop hInf in
theorem cofiltered (T : C) : IsCofiltered (Objects P T) where
  nonempty := ⟨⟨⊤, hTop T⟩⟩
  cone_objs U V :=
    ⟨⟨U.obj ⊓ V.obj, hInf U.obj V.obj T U.property V.property⟩,
      ObjectProperty.homMk (homOfLE inf_le_left), ObjectProperty.homMk (homOfLE inf_le_right), trivial⟩
  cone_maps U V f g := ⟨U, 𝟙 U, by
    apply (Neighborhoods.property P T).ι.map_injective
    exact Subsingleton.elim _ _⟩

variable (hIncoming : ∀ V {T U : C}, (T ⟶ U) → P V U → P V T)

def change {T U : C} (α : T ⟶ U) : Objects P U ⥤ Objects P T :=
  ObjectProperty.ιOfLE (fun V hV => hIncoming V α hV)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Neighborhoods
