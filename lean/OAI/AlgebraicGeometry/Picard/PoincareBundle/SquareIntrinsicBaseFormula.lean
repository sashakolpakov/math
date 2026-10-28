import OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareIntrinsicFiberFormula

/-! # Square Intrinsic Base Formula -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareIntrinsicBaseFormula.Intrinsic

noncomputable section

/-! The native square formula with a separately specified original quotient point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : iX ≫ f = f' ≫ iY)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))

/-- Specifying the original quotient point changes only its equality proof. -/
theorem hom_to {T : Scheme.{u}} (q : T ⟶ Y') (x y : T ⟶ X')
    (hx : x ≫ f' = q) (hy : y ≫ f' = q) (q₀ : T ⟶ Y) (hq : q ≫ iY = q₀)
    (a b : T ⟶ X) (ha : x ≫ iX = a) (hb : y ≫ iX = b)
    (hqa : a ≫ f = q₀) (hqb : b ≫ f = q₀) :
    (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f' (Ordinary.SquareGluing.pulledDatum f f' iX iY hf D)).hom q x y hx hy =
      (PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks iX (D.obj PUnit.unit) x a ha).hom ≫
        (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D).hom q₀ a b hqa hqb ≫
          (PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks iX (D.obj PUnit.unit) y b hb).inv := by
  subst q₀
  exact SquareIntrinsicFiberFormula.Intrinsic.hom_to f f' iX iY hf D q x y hx hy a b ha hb hqa hqb

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareIntrinsicBaseFormula.Intrinsic
