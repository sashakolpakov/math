import Mathlib.CategoryTheory.Iso

/-! # Isomorphism Hom Subtype -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IsomorphismHomSubtype.Construction

noncomputable section

/-! An isomorphism is equivalently a morphism that is invertible. -/

open _root_.CategoryTheory

universe u v

def isoHomSubtypeEquiv {C : Type u} [Category.{v} C] (A B : C) :
    (A ≅ B) ≃ { f : A ⟶ B // IsIso f } where
  toFun e := ⟨e.hom, inferInstance⟩
  invFun f := by
    haveI := f.property
    exact asIso f.val
  left_inv _ := Iso.ext rfl
  right_inv _ := Subtype.ext rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IsomorphismHomSubtype.Construction
