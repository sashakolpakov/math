import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterTranslations

/-! # Parameter Intrinsic Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterIntrinsicDescent.Intrinsic

noncomputable section

/-! Parameter restriction preserves the full native gluing maps through the actual fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear

variable {S : Scheme.{u}} {K A X Y : Over S} (t : K ⟶ A) (g : X ⟶ Y)

/-- A lifted parameter point has the corresponding image under the original coordinate cover. -/
theorem image_cover {T : Over S} (x : T ⟶ K) (z : T ⟶ X) (q : T ⟶ K ⊗ Y)
    (hz : lift x z ≫ (𝟙 K ⊗ₘ g) = q) :
    lift (x ≫ t) z ≫ (𝟙 A ⊗ₘ g) = q ≫ (t ⊗ₘ 𝟙 Y) := by
  calc
    _ = (lift x z ≫ (𝟙 K ⊗ₘ g)) ≫ (t ⊗ₘ 𝟙 Y) := by simp
    _ = _ := congrArg (fun v => v ≫ (t ⊗ₘ 𝟙 Y)) hz

variable [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- Restricting the parameter conjugates the actual native translation gluing map. -/
theorem hom_translation {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ K)
    (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) (q : T ⟶ K ⊗ Y)
    (hz : lift x z ≫ (𝟙 K ⊗ₘ g) = q) (hw : lift x w ≫ (𝟙 K ⊗ₘ g) = q) :
    (ParameterKernelFrames.nativeDatum t g L Dv Kv).hom q.left (lift x z).left (lift x w).left
      (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L (lift x z) (lift (x ≫ t) z) (by simp)).hom ≫
      (KernelDescent.nativeDatum g L Dv Kv).hom
        (q ≫ (t ⊗ₘ 𝟙 Y)).left (lift (x ≫ t) z).left (lift (x ≫ t) w).left
        (congrArg Over.Hom.left (image_cover t g x z q hz))
        (congrArg Over.Hom.left (image_cover t g x w q hw)) ≫
      (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L (lift x w) (lift (x ≫ t) w) (by simp)).inv := by
  unfold ParameterKernelFrames.nativeDatum
  rw [DescentTranslation.native_hom_translation g (L.pullback (t ⊗ₘ 𝟙 X).left)
      (ParameterKernelFrames.multiplication t L Dv) (ParameterKernelFrames.frames t g L Dv Kv) l z w x h q hz hw,
    DescentTranslation.native_hom_translation g L Dv Kv l z w (x ≫ t) h
      (q ≫ (t ⊗ₘ 𝟙 Y)) (image_cover t g x z q hz) (image_cover t g x w q hw)]
  exact ParameterTranslations.translation_eq t g L Dv Kv l z w x h (by simp) (by simp)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterIntrinsicDescent.Intrinsic
