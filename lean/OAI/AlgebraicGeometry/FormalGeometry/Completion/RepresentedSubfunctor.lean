import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Represented Subfunctor -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctor.Construction

noncomputable section

/-! A represented subfunctor has a canonical representing monomorphism
and its factorization criterion is the original pointwise predicate. -/

open _root_.CategoryTheory Opposite

universe u v
variable {C : Type u} [Category.{v} C] {S : C} (P : Subfunctor (yoneda.obj S))
  [P.toFunctor.IsRepresentable]

def representedSubfunctorFamily : Over S := Over.mk P.toFunctor.reprx.val

theorem representedSubfunctor_value {T : C} (f : T ⟶ (representedSubfunctorFamily P).left) :
    (P.toFunctor.representableBy.homEquiv f).val = f ≫ (representedSubfunctorFamily P).hom :=
  congrArg Subtype.val (P.toFunctor.representableBy.homEquiv_eq f)

instance representedSubfunctorFamily_mono : Mono (representedSubfunctorFamily P).hom := by
  constructor
  intro T f g hfg
  apply P.toFunctor.representableBy.homEquiv.injective
  apply Subtype.ext
  rw [representedSubfunctor_value, representedSubfunctor_value]
  exact hfg

theorem representedSubfunctor_factorization (T : C) (f : T ⟶ S) :
    f ∈ P.obj (op T) ↔ ∃ g : T ⟶ (representedSubfunctorFamily P).left,
      g ≫ (representedSubfunctorFamily P).hom = f := by
  constructor
  · intro hf
    let g := P.toFunctor.representableBy.homEquiv.symm ⟨f, hf⟩
    refine ⟨g, (representedSubfunctor_value P g).symm.trans ?_⟩
    exact congrArg Subtype.val (P.toFunctor.representableBy.homEquiv.apply_symm_apply ⟨f, hf⟩)
  · rintro ⟨g, hg⟩
    have h := (P.toFunctor.representableBy.homEquiv g).property
    rw [representedSubfunctor_value, hg] at h
    exact h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RepresentedSubfunctor.Construction
