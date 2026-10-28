import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.DescentTranslation

/-! # Parameter Translations -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterTranslations

noncomputable section

/-! Actual parameter restriction conjugates the vertical kernel action through geometric fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear

variable {S : Scheme.{u}} {K A X Y : Over S} [GrpObj X] [GrpObj Y]
  (t : K ⟶ A) (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The parameter product can be written at three explicitly specified target points. -/
theorem product_eq_to {T : Over S} (a b c : T ⟶ K ⊗ X)
    (h : FiberwiseMultiplication.ProductRel (snd K X) (fst K X) a b c) (a' b' c' : T ⟶ A ⊗ X)
    (ha : a ≫ (t ⊗ₘ 𝟙 X) = a') (hb : b ≫ (t ⊗ₘ 𝟙 X) = b') (hc : c ≫ (t ⊗ₘ 𝟙 X) = c')
    (h' : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) a' b' c') :
    (ParameterKernelFrames.multiplication t L Dv).product a b c h =
      Pulled.LineBilinear.transport (t ⊗ₘ 𝟙 X) L a b c a' b' c' ha hb hc (Dv.product a' b' c' h') := by
  subst a'
  subst b'
  subst c'
  exact ParameterProducts.product_eq t L Dv a b c h

/-- The actual frame comparison also retains a specified target point. -/
theorem frame_eq_to {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (a : T ⟶ K ⊗ X)
    (ha : l ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd K X) (b : T ⟶ A ⊗ X)
    (hb : a ≫ (t ⊗ₘ 𝟙 X) = b) (hl : l ≫ Kernel.Scheme.kernelInclusion g = b ≫ snd A X) :
    (ParameterKernelFrames.frames t g L Dv Kv).frame l a ha =
      Pulled.LineSection.transportFrame (t ⊗ₘ 𝟙 X) L a b hb (Kv.frame l b hl) := by
  subst b
  exact ParameterKernelFrames.frames_frame t g L Dv Kv l a ha hl

/-- Inserting the parameter kernel frame gives the conjugate of the original actual translation. -/
theorem translation_eq {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ K)
    (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w)
    (hz : lift x z ≫ (t ⊗ₘ 𝟙 X) = lift (x ≫ t) z)
    (hw : lift x w ≫ (t ⊗ₘ 𝟙 X) = lift (x ≫ t) w) :
    CoordinateTransverseTranslations.verticalTranslateTo (L.pullback (t ⊗ₘ 𝟙 X).left) (ParameterKernelFrames.multiplication t L Dv) g (ParameterKernelFrames.frames t g L Dv Kv)
      l z w x h =
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L (lift x z) (lift (x ≫ t) z) hz).hom ≫
      CoordinateTransverseTranslations.verticalTranslateTo L Dv g Kv l z w (x ≫ t) h ≫
        (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L (lift x w) (lift (x ≫ t) w) hw).inv := by
  have hc : lift x (l ≫ Kernel.Scheme.kernelInclusion g) ≫ (t ⊗ₘ 𝟙 X) = lift (x ≫ t) (l ≫ Kernel.Scheme.kernelInclusion g) := by simp
  unfold CoordinateTransverseTranslations.verticalTranslateTo CoordinateTransverseTranslations.verticalProductTo
  rw [product_eq_to t L Dv _ _ _ (CoordinateTransverseTranslations.verticalRel _ _ _ _ h) _ _ _ hc hz hw (CoordinateTransverseTranslations.verticalRel _ _ _ _ h),
    frame_eq_to t g L Dv Kv l _ (lift_snd _ _).symm _ hc (lift_snd _ _).symm]
  exact Bilinear.Transport.contractLeft_transport (Dv.product _ _ _ (CoordinateTransverseTranslations.verticalRel _ _ _ _ h))
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L _ _ hc).symm
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L _ _ hz).symm
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L _ _ hw).symm
    (Kv.frame l _ (lift_snd _ _).symm).hom

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterTranslations
