import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterIntrinsicDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.FiberIsoNaturality

/-! # Parameter Intrinsic Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterIntrinsicCompatibility.Intrinsic

noncomputable section

/-! A morphism of actual coordinate descents remains compatible after arbitrary parameter restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

section

/-- Four comparison squares transport the compatibility of two gluing morphisms. -/
theorem conjugate_compatible {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ U₁ U₂ V₁ V₂ : C}
    (c₁ : X₁ ≅ U₁) (c₂ : X₂ ≅ U₂) (d₁ : Y₁ ≅ V₁) (d₂ : Y₂ ≅ V₂)
    (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂) (b₁ : U₁ ⟶ V₁) (b₂ : U₂ ⟶ V₂)
    (r : U₁ ⟶ U₂) (s : V₁ ⟶ V₂)
    (h₁ : a₁ ≫ d₁.hom = c₁.hom ≫ b₁) (h₂ : a₂ ≫ d₂.hom = c₂.hom ≫ b₂)
    (h : b₁ ≫ s = r ≫ b₂) :
    a₁ ≫ d₁.hom ≫ s ≫ d₂.inv = (c₁.hom ≫ r ≫ c₂.inv) ≫ a₂ := by
  have h₂' := Bilinear.PullbackNaturality.inverse_square c₂ d₂ a₂ b₂ h₂
  calc
    _ = c₁.hom ≫ b₁ ≫ s ≫ d₂.inv := by rw [← Category.assoc a₁ d₁.hom, h₁, Category.assoc]
    _ = c₁.hom ≫ r ≫ b₂ ≫ d₂.inv := by rw [← Category.assoc b₁ s, h, Category.assoc]
    _ = _ := by rw [← h₂']; simp only [Category.assoc]

end

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear

variable {S : Scheme.{u}} {K A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (t : K ⟶ A) (g : X ⟶ Y) [IsMonHom g]
  (L M : Line.Bundles.LineBundle (A ⊗ X).left) (e : L.sheaf ≅ M.sheaf)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L) (Ev : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) M)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv) (Jv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) M g Ev)
  (he : ∀ (T : Over S) (q : T ⟶ A ⊗ Y) (a b : T ⟶ A ⊗ X)
    (ha : a ≫ (𝟙 A ⊗ₘ g) = q) (hb : b ≫ (𝟙 A ⊗ₘ g) = q),
    (Scheme.Modules.pullback a.left).map e.hom ≫ (Vertical.KernelDescent.nativeDatum g M Ev Jv).hom
      q.left a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb) =
    (Vertical.KernelDescent.nativeDatum g L Dv Kv).hom
      q.left a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb) ≫
        (Scheme.Modules.pullback b.left).map e.hom)

include he

/-- Arbitrary parameter schemes retain actual native compatibility at every kernel translation. -/
theorem hom_translation {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ K)
    (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) (q : T ⟶ K ⊗ Y)
    (hz : lift x z ≫ (𝟙 K ⊗ₘ g) = q) (hw : lift x w ≫ (𝟙 K ⊗ₘ g) = q) :
    (Scheme.Modules.pullback (lift x z).left).map ((Scheme.Modules.pullback (t ⊗ₘ 𝟙 X).left).map e.hom) ≫
      (Vertical.ParameterKernelFrames.nativeDatum t g M Ev Jv).hom q.left (lift x z).left (lift x w).left
        (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
    (Vertical.ParameterKernelFrames.nativeDatum t g L Dv Kv).hom q.left (lift x z).left (lift x w).left
      (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) ≫
        (Scheme.Modules.pullback (lift x w).left).map ((Scheme.Modules.pullback (t ⊗ₘ 𝟙 X).left).map e.hom) := by
  rw [Vertical.ParameterIntrinsicDescent.Intrinsic.hom_translation t g M Ev Jv l z w x h q hz hw,
    Vertical.ParameterIntrinsicDescent.Intrinsic.hom_translation t g L Dv Kv l z w x h q hz hw]
  exact conjugate_compatible
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L (lift x z) (lift (x ≫ t) z) (by simp))
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L (lift x w) (lift (x ≫ t) w) (by simp))
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) M (lift x z) (lift (x ≫ t) z) (by simp))
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) M (lift x w) (lift (x ≫ t) w) (by simp))
    _ _ _ _ _ _
    (Pulled.FiberIsoNaturality.comparison_hom (t ⊗ₘ 𝟙 X) L M e.hom _ _ (by simp))
    (Pulled.FiberIsoNaturality.comparison_hom (t ⊗ₘ 𝟙 X) L M e.hom _ _ (by simp))
    (he T (q ≫ (t ⊗ₘ 𝟙 Y)) (lift (x ≫ t) z) (lift (x ≫ t) w)
      (Vertical.ParameterIntrinsicDescent.Intrinsic.image_cover t g x z q hz)
      (Vertical.ParameterIntrinsicDescent.Intrinsic.image_cover t g x w q hw))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterIntrinsicCompatibility.Intrinsic
