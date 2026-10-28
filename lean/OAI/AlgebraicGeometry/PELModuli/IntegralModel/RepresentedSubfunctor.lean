import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Represented Subfunctor -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.RepresentedSubfunctor

noncomputable section

/-! Extract the universal object and exact classifying property from a
natural representation of a subfunctor. -/

open _root_.CategoryTheory Opposite

universe u v
variable {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type v) (Q : Subfunctor F)
  (Z : C) (e : yoneda.obj Z ≅ Q.toFunctor)

def representedSubfunctorUniversal : F.obj (op Z) :=
  (e.hom.app (op Z) (𝟙 Z)).val

theorem representedSubfunctorUniversal_mem :
    representedSubfunctorUniversal F Q Z e ∈ Q.obj (op Z) :=
  (e.hom.app (op Z) (𝟙 Z)).property

theorem representedSubfunctorUniversal_naturality {T : C} (f : T ⟶ Z) :
    (e.hom.app (op T) f).val = F.map f.op (representedSubfunctorUniversal F Q Z e) := by
  have h := ConcreteCategory.congr_hom (e.hom.naturality f.op) (𝟙 Z)
  change e.hom.app (op T) (f ≫ 𝟙 Z) =
    Q.toFunctor.map f.op (e.hom.app (op Z) (𝟙 Z)) at h
  rw [Category.comp_id] at h
  exact congrArg Subtype.val h

theorem representedSubfunctorUniversal_classifies (T : C) (x : F.obj (op T)) :
    x ∈ Q.obj (op T) ↔
      ∃! f : T ⟶ Z, F.map f.op (representedSubfunctorUniversal F Q Z e) = x := by
  have he := ConcreteCategory.bijective_of_isIso (e.hom.app (op T))
  constructor
  · intro hx
    obtain ⟨f, hf⟩ := he.surjective ⟨x, hx⟩
    change T ⟶ Z at f
    refine ⟨f, ?_, ?_⟩
    · change F.map f.op (representedSubfunctorUniversal F Q Z e) = x
      rw [← representedSubfunctorUniversal_naturality, hf]
    · intro a ha
      apply he.injective
      apply Subtype.ext
      rw [representedSubfunctorUniversal_naturality, ha, hf]
  · rintro ⟨f, hf, _⟩
    rw [← hf]
    exact Q.map f.op (representedSubfunctorUniversal_mem F Q Z e)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.RepresentedSubfunctor
