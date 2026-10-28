import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicationSquareProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.UnitContraction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.DescentTranslation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.PullbackLineDescent

/-! # Vertical Unit Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.VerticalUnitDescent

noncomputable section

/-! The pulled target unit law identifies coordinate descent with native canonical line descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrameIsotropy
open OAI.AlgebraicGeometry.Picard.PoincareBundle.CoordinateTransverseTranslations OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent

variable {S : Scheme.{u}} {A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (g : X ⟶ Y) [IsMonHom g] (L : Line.Bundles.LineBundle (A ⊗ Y).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A Y) (fst A Y) L)
  (K : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) (L.pullback (𝟙 A ⊗ₘ g).left) g
    (KernelFrameIsotropy.verticalMultiplication (𝟙 A) g L Dv))

/-- Inserting the pulled target unit gives exactly canonical gluing between two lifted points. -/
theorem hom_translation {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ A)
    (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) (q : T ⟶ A ⊗ Y)
    (hz : lift x z ≫ (𝟙 A ⊗ₘ g) = q) (hw : lift x w ≫ (𝟙 A ⊗ₘ g) = q)
    (hd : lift x (l ≫ Kernel.Scheme.kernelInclusion g) ≫ (𝟙 A ⊗ₘ g) = lift x 1)
    (hu : K.frame l (lift x (l ≫ Kernel.Scheme.kernelInclusion g)) (lift_snd _ _).symm =
      LineSection.transportFrame (𝟙 A ⊗ₘ g) L
        (lift x (l ≫ Kernel.Scheme.kernelInclusion g)) (lift x 1) hd (Dv.unitFrame (lift x 1) (lift_snd _ _))) :
    (Vertical.KernelDescent.nativeDatum g (L.pullback (𝟙 A ⊗ₘ g).left) (KernelFrameIsotropy.verticalMultiplication (𝟙 A) g L Dv) K).hom
      q.left (lift x z).left (lift x w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
    (Homomorphisms.LineKernelCocycle.Construction.pullbackLineNativeDatum (𝟙 A ⊗ₘ g) (Line.Comparison.Bundle.toShared L)).hom
      q.left (lift x z).left (lift x w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) := by
  have hq : q ≫ fst A Y = x := by
    rw [← hz]
    simp
  have hp : FiberwiseMultiplication.ProductRel (snd A Y) (fst A Y) (lift x 1) q q := by
    exact ⟨by simp, by simpa only [lift_fst] using hq.symm,
      by simpa only [lift_fst] using hq.symm⟩
  rw [Vertical.DescentTranslation.native_hom_translation g (L.pullback (𝟙 A ⊗ₘ g).left)
    (KernelFrameIsotropy.verticalMultiplication (𝟙 A) g L Dv) K l z w x h q hz hw,
    Intrinsic.PullbackLineDescent.hom_eq (𝟙 A ⊗ₘ g) L q (lift x z) (lift x w) hz hw]
  unfold CoordinateTransverseTranslations.verticalTranslateTo CoordinateTransverseTranslations.verticalProductTo
  rw [show (KernelFrameIsotropy.verticalMultiplication (𝟙 A) g L Dv).product
      (lift x (l ≫ Kernel.Scheme.kernelInclusion g)) (lift x z) (lift x w) (CoordinateTransverseTranslations.verticalRel _ _ _ _ h) =
      LineBilinear.transport (𝟙 A ⊗ₘ g) L
        (lift x (l ≫ Kernel.Scheme.kernelInclusion g)) (lift x z) (lift x w) (lift x 1) q q hd hz hw
        (Dv.product (lift x 1) q q hp) from
      MultiplicationSquareProducts.product_eq_to (snd A X) (fst A X) (snd A Y) (fst A Y)
        (𝟙 A ⊗ₘ g) g (𝟙 A) (by simp) (by simp) L Dv
        _ _ _ (CoordinateTransverseTranslations.verticalRel _ _ _ _ h) _ _ _ hd hz hw hp, hu]
  exact UnitContraction.contraction_eq (snd A Y) (fst A Y) (𝟙 A ⊗ₘ g) L Dv
    _ _ _ _ _ hd hz hw (lift_snd _ _) hp

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.VerticalUnitDescent
