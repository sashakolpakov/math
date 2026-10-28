import OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterIntrinsicCompatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.TranslationTests
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.DescentIso

/-! # Parameter Intrinsic Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterIntrinsicIso.Intrinsic

noncomputable section

/-! Complete coordinate-descent isomorphisms restrict to arbitrary parameter schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent

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

/-- The pulled original sheaf isomorphism gives an actual isomorphism of parameter descent data. -/
def iso :
    Vertical.KernelDescent.ordinaryDatum g (L.pullback (t ⊗ₘ 𝟙 X).left) (Vertical.ParameterKernelFrames.multiplication t L Dv) (Vertical.ParameterKernelFrames.frames t g L Dv Kv) ≅
      Vertical.KernelDescent.ordinaryDatum g (M.pullback (t ⊗ₘ 𝟙 X).left) (Vertical.ParameterKernelFrames.multiplication t M Ev) (Vertical.ParameterKernelFrames.frames t g M Ev Jv) :=
  Intrinsic.DescentIso.iso_of_over (𝟙 K ⊗ₘ g) _ _ ((Scheme.Modules.pullback (t ⊗ₘ 𝟙 X).left).mapIso e) (by
    intro T q a b ha hb
    exact Intrinsic.TranslationTests.hom_compatible g
      (Vertical.ParameterKernelFrames.nativeDatum t g L Dv Kv)
      (Vertical.ParameterKernelFrames.nativeDatum t g M Ev Jv)
      ((Scheme.Modules.pullback (t ⊗ₘ 𝟙 X).left).mapIso e)
      (fun T l z w x h q hz hw => ParameterIntrinsicCompatibility.Intrinsic.hom_translation t g L M e Dv Ev Kv Jv he
        l z w x h q hz hw) q a b ha hb)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterIntrinsicIso.Intrinsic
