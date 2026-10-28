import OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquarePointFormula

/-! # Parameter Square Intrinsic -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareIntrinsic.Intrinsic

noncomputable section

/-! Actual parameter-kernel descent agrees with native pullback of the original descent datum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareData

variable {S : Scheme.{u}} {K A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (t : K ⟶ A) (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The square pullback has the original native gluing map between the specified image points. -/
theorem square_hom {T : Over S} (z w : T ⟶ X) (x : T ⟶ K) (q : T ⟶ K ⊗ Y)
    (hz : lift x z ≫ (𝟙 K ⊗ₘ g) = q) (hw : lift x w ≫ (𝟙 K ⊗ₘ g) = q) :
    (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor (𝟙 K ⊗ₘ g).left (ParameterSquareData.squareDatum t g L Dv Kv)).hom
      q.left (lift x z).left (lift x w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L (lift x z) (lift (x ≫ t) z) (by simp)).hom ≫
      (Vertical.KernelDescent.nativeDatum g L Dv Kv).hom
        (q ≫ (t ⊗ₘ 𝟙 Y)).left (lift (x ≫ t) z).left (lift (x ≫ t) w).left
        (congrArg Over.Hom.left (Vertical.ParameterIntrinsicDescent.Intrinsic.image_cover t g x z q hz))
        (congrArg Over.Hom.left (Vertical.ParameterIntrinsicDescent.Intrinsic.image_cover t g x w q hw)) ≫
      (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L (lift x w) (lift (x ≫ t) w) (by simp)).inv :=
  ParameterSquarePointFormula.hom_eq t g L Dv Kv q (lift x z) (lift x w) hz hw
    (q ≫ (t ⊗ₘ 𝟙 Y)) (lift (x ≫ t) z) (lift (x ≫ t) w) rfl (by simp) (by simp)
    (Vertical.ParameterIntrinsicDescent.Intrinsic.image_cover t g x z q hz)
    (Vertical.ParameterIntrinsicDescent.Intrinsic.image_cover t g x w q hw)

/-- At every actual kernel translation, parameter descent is precisely the ordinary square pullback. -/
theorem hom_translation {T : Over S} (l : T ⟶ Kernel.Scheme.kernelObject g) (z w : T ⟶ X) (x : T ⟶ K)
    (h : (l ≫ Kernel.Scheme.kernelInclusion g) * z = w) (q : T ⟶ K ⊗ Y)
    (hz : lift x z ≫ (𝟙 K ⊗ₘ g) = q) (hw : lift x w ≫ (𝟙 K ⊗ₘ g) = q) :
    (Vertical.ParameterKernelFrames.nativeDatum t g L Dv Kv).hom q.left (lift x z).left (lift x w).left
      (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) =
    (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor (𝟙 K ⊗ₘ g).left (ParameterSquareData.squareDatum t g L Dv Kv)).hom
      q.left (lift x z).left (lift x w).left (congrArg Over.Hom.left hz) (congrArg Over.Hom.left hw) :=
  (Vertical.ParameterIntrinsicDescent.Intrinsic.hom_translation t g L Dv Kv l z w x h q hz hw).trans
    (square_hom t g L Dv Kv z w x q hz hw).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareIntrinsic.Intrinsic
