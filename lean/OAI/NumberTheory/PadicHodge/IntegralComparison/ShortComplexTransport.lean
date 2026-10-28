import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Short Complex Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ShortComplexTransport

noncomputable section

/-!
# IntegralComparison: transporting a short exact diagram through specified object isomorphisms
-/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] (S : ShortComplex C)
  {X Y Z : C} (e₁ : S.X₁ ≅ X) (e₂ : S.X₂ ≅ Y) (e₃ : S.X₃ ≅ Z)

def sequence : ShortComplex C :=
  ShortComplex.mk (e₁.inv ≫ S.f ≫ e₂.hom) (e₂.inv ≫ S.g ≫ e₃.hom) (by
    simp [Category.assoc])

def iso : S ≅ sequence S e₁ e₂ e₃ :=
  ShortComplex.isoMk e₁ e₂ e₃ (by simp [sequence]) (by simp [sequence])

theorem exact (hS : S.Exact) : (sequence S e₁ e₂ e₃).Exact :=
  ShortComplex.exact_of_iso (iso S e₁ e₂ e₃) hS

theorem mono_f [Mono S.f] : Mono (sequence S e₁ e₂ e₃).f := by
  change Mono (e₁.inv ≫ S.f ≫ e₂.hom)
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ShortComplexTransport
