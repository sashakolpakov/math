import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.PullbackLineDescent

/-! # Square Intrinsic Fiber Formula -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareIntrinsicFiberFormula.Intrinsic

noncomputable section

/-! Native square descent at specified image points is the original gluing through actual fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : iX ≫ f = f' ≫ iY)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))

/-- Specified image points give the complete native pulled gluing formula. -/
theorem hom_to {T : Scheme.{u}} (q : T ⟶ Y') (x y : T ⟶ X')
    (hx : x ≫ f' = q) (hy : y ≫ f' = q) (a b : T ⟶ X)
    (ha : x ≫ iX = a) (hb : y ≫ iX = b)
    (hqa : a ≫ f = q ≫ iY) (hqb : b ≫ f = q ≫ iY) :
    (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f' (Ordinary.SquareGluing.pulledDatum f f' iX iY hf D)).hom q x y hx hy =
      (PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks iX (D.obj PUnit.unit) x a ha).hom ≫
        (Homomorphisms.IntrinsicModuleDescent.Construction.NativeModuleDescent.ofPseudofunctor f D).hom (q ≫ iY) a b hqa hqb ≫
          (PullbackFiberComposition.fiberIsoTo Geometric.KernelLinearization.modulePullbacks iX (D.obj PUnit.unit) y b hb).inv := by
  subst a
  subst b
  change (Ordinary.SquareGluing.pulledDatum f f' iX iY hf D).hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
    (Scheme.Modules.pullbackComp x iX).hom.app (D.obj PUnit.unit) ≫
      D.hom (q ≫ iY) (i₁ := PUnit.unit) (i₂ := PUnit.unit) (x ≫ iX) (y ≫ iX) hqa hqb ≫
        (Scheme.Modules.pullbackComp y iX).inv.app (D.obj PUnit.unit)
  exact Ordinary.SquareGluing.pulledHom f f' iX iY hf D q x y hx hy

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SquareIntrinsicFiberFormula.Intrinsic
