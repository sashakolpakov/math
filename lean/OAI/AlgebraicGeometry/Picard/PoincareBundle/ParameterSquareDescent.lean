import OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareIntrinsic
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.TranslationTests
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.DescentIso

/-! # Parameter Square Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareDescent

noncomputable section

/-! The constructed parameter descent is the ordinary square pullback as a complete descent object. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareData
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterKernelFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent

variable {S : Scheme.{u}} {K A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (t : K ⟶ A) (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The identity on the pulled line intertwines the entire two presentations of parameter descent. -/
def iso : ParameterSquareData.squareDatum t g L Dv Kv ≅
    Vertical.KernelDescent.ordinaryDatum g (L.pullback (t ⊗ₘ 𝟙 X).left) (Vertical.ParameterKernelFrames.multiplication t L Dv) (Vertical.ParameterKernelFrames.frames t g L Dv Kv) :=
  Ordinary.DescentIso.iso_of_over (𝟙 K ⊗ₘ g) _ _ (Iso.refl _) (by
    intro T q a b ha hb
    apply Intrinsic.TranslationTests.hom_compatible g
      (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor (𝟙 K ⊗ₘ g).left (ParameterSquareData.squareDatum t g L Dv Kv))
      (Vertical.ParameterKernelFrames.nativeDatum t g L Dv Kv) (Iso.refl _) _ q a b ha hb
    intro U l z w x h q hz hw
    simp only [Iso.refl_hom]
    erw [(Scheme.Modules.pullback (lift x z).left).map_id,
      (Scheme.Modules.pullback (lift x w).left).map_id, Category.id_comp, Category.comp_id]
    exact ParameterSquareIntrinsic.Intrinsic.hom_translation t g L Dv Kv l z w x h q hz hw)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareDescent
