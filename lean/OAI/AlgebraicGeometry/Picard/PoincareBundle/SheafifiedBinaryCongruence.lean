import Mathlib.CategoryTheory.Sites.LocallyInjective

/-! # Sheafified Binary Congruence -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SheafifiedBinaryCongruence

noncomputable section

/-! A natural binary operation respects equality after sheafification, by local injectivity. -/

open _root_.CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {F : Cᵒᵖ ⥤ Type w} (G : Sheaf J (Type w)) (η : F ⟶ G.obj)
  [Presheaf.IsLocallyInjective J η]
  (μ : ∀ X, F.obj X → F.obj X → F.obj X)
  (hμ : ∀ {X Y} (f : X ⟶ Y) (x y : F.obj X), F.map f (μ X x y) = μ Y (F.map f x) (F.map f y))

include hμ

/-- Equality in a sheaf is preserved by every natural presheaf binary operation. -/
theorem binary_congr {X : Cᵒᵖ} {x x' y y' : F.obj X}
    (hx : η.app X x = η.app X x') (hy : η.app X y = η.app X y') :
    η.app X (μ X x y) = η.app X (μ X x' y') := by
  let K : J.Cover X.unop := ⟨Presheaf.equalizerSieve (F := F) x x' ⊓ Presheaf.equalizerSieve (F := F) y y',
    J.intersection_covering (Presheaf.equalizerSieve_mem J η x x' hx)
      (Presheaf.equalizerSieve_mem J η y y' hy)⟩
  let a : PUnit.{w + 1} ⟶ G.obj.obj X := ↾(fun _ => η.app X (μ X x y))
  let b : PUnit.{w + 1} ⟶ G.obj.obj X := ↾(fun _ => η.app X (μ X x' y'))
  have hab : a = b := G.property.hom_ext K a b (by
    intro I
    apply ConcreteCategory.ext_apply
    intro z
    change G.obj.map I.f.op (η.app X (μ X x y)) = G.obj.map I.f.op (η.app X (μ X x' y'))
    rw [← η.naturality_apply, ← η.naturality_apply, hμ, hμ]
    have h₁ : F.map I.f.op x = F.map I.f.op x' := I.hf.1
    have h₂ : F.map I.f.op y = F.map I.f.op y' := I.hf.2
    rw [h₁, h₂])
  exact congrArg (fun c => c PUnit.unit) hab

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SheafifiedBinaryCongruence
