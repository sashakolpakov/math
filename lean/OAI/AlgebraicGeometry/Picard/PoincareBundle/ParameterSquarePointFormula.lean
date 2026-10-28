import OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareData
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareIntrinsicBaseFormula

/-! # Parameter Square Point Formula -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquarePointFormula

noncomputable section

/-! Parameter square descent expressed at arbitrary separately named original-base test points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareData

variable {S : Scheme.{u}} {K A X Y : Over S} [GrpObj X] [IsCommMonObj X] [GrpObj Y]
  (t : K ⟶ A) (g : X ⟶ Y) [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The native square gluing is the original map through the actual fiber comparisons. -/
theorem hom_eq {T : Over S} (q : T ⟶ K ⊗ Y) (x y : T ⟶ K ⊗ X)
    (hx : x ≫ (𝟙 K ⊗ₘ g) = q) (hy : y ≫ (𝟙 K ⊗ₘ g) = q)
    (q₀ : T ⟶ A ⊗ Y) (a b : T ⟶ A ⊗ X)
    (hq : q ≫ (t ⊗ₘ 𝟙 Y) = q₀) (ha : x ≫ (t ⊗ₘ 𝟙 X) = a) (hb : y ≫ (t ⊗ₘ 𝟙 X) = b)
    (hqa : a ≫ (𝟙 A ⊗ₘ g) = q₀) (hqb : b ≫ (𝟙 A ⊗ₘ g) = q₀) :
    (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor (𝟙 K ⊗ₘ g).left (ParameterSquareData.squareDatum t g L Dv Kv)).hom
      q.left x.left y.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L x a ha).hom ≫
      (Vertical.KernelDescent.nativeDatum g L Dv Kv).hom q₀.left a.left b.left
        (congrArg Over.Hom.left hqa) (congrArg Over.Hom.left hqb) ≫
      (Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L y b hb).inv := by
  have hs := SquareIntrinsicBaseFormula.Intrinsic.hom_to (𝟙 A ⊗ₘ g).left (𝟙 K ⊗ₘ g).left
    (t ⊗ₘ 𝟙 X).left (t ⊗ₘ 𝟙 Y).left (congrArg Over.Hom.left (ParameterSquareData.square t g))
    (Vertical.KernelDescent.ordinaryDatum g L Dv Kv) q.left x.left y.left
    (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) q₀.left (congrArg Over.Hom.left hq)
    a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb)
    (congrArg Over.Hom.left hqa) (congrArg Over.Hom.left hqb)
  have hca : PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks (t ⊗ₘ 𝟙 X).left
      ((Vertical.KernelDescent.ordinaryDatum g L Dv Kv).obj PUnit.unit) x.left a.left
      (congrArg Over.Hom.left ha) = Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L x a ha :=
    ParameterSquareData.comparison_eq (t ⊗ₘ 𝟙 X) L x a ha
  have hcb : PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks (t ⊗ₘ 𝟙 X).left
      ((Vertical.KernelDescent.ordinaryDatum g L Dv Kv).obj PUnit.unit) y.left b.left
      (congrArg Over.Hom.left hb) = Pulled.LineBilinear.fiberComparison (t ⊗ₘ 𝟙 X) L y b hb :=
    ParameterSquareData.comparison_eq (t ⊗ₘ 𝟙 X) L y b hb
  rw [hca, hcb] at hs
  exact hs

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquarePointFormula
