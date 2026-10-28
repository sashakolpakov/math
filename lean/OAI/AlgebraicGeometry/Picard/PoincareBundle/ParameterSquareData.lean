import OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareIntrinsicFiberFormula
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ParameterIntrinsicDescent

/-! # Parameter Square Data -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareData

noncomputable section

/-! The actual parameter square and its ordinary pulled descent datum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.LineBilinear OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

/-- Ordinary and original-base pullback comparisons give the same sheaf isomorphism. -/
theorem comparison_eq {S : Scheme.{u}} {K E : Over S} (p : K ⟶ E)
    (L : Line.Bundles.LineBundle E.left) {T : Over S} (x : T ⟶ K) (a : T ⟶ E) (hx : x ≫ p = a) :
    PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks p.left L.sheaf x.left a.left
      (congrArg Over.Hom.left hx) = Pulled.LineBilinear.fiberComparison p L x a hx := by
  rw [Intrinsic.PullbackLineDescent.scheme_comparison]
  exact (GlobalPullbackFrame.comparison_eq p L x a hx).symm

variable {S : Scheme.{u}} {K A X Y : Over S} (t : K ⟶ A) (g : X ⟶ Y)

/-- Parameter change commutes with the second-coordinate quotient. -/
theorem square : (t ⊗ₘ 𝟙 X) ≫ (𝟙 A ⊗ₘ g) = (𝟙 K ⊗ₘ g) ≫ (t ⊗ₘ 𝟙 Y) := by
  simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

variable [GrpObj X] [IsCommMonObj X] [GrpObj Y] [IsMonHom g]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The actual ordinary descent pullback through the parameter square. -/
def squareDatum := Ordinary.SquareGluing.pulledDatum
  (𝟙 A ⊗ₘ g).left (𝟙 K ⊗ₘ g).left (t ⊗ₘ 𝟙 X).left (t ⊗ₘ 𝟙 Y).left
  (congrArg Over.Hom.left (square t g)) (Vertical.KernelDescent.ordinaryDatum g L Dv Kv)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ParameterSquareData
