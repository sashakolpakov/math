import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.ReducedCartesianRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.SectionFibers

/-! # Product Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProductRigidity

noncomputable section

/-! Product rigidity for a proper smooth geometrically connected factor over a field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}}

theorem smoothProperProductMap_rigidity (p : X ⟶ Spec (.of K)) (q : Y ⟶ Spec (.of K))
    [UniversallyClosed p] [Smooth p] [GeometricallyConnected p]
    [PreconnectedSpace Y] [IsReduced (pullback p q)]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    (y : Spec (.of K) ⟶ Y) (hy : y ≫ q = 𝟙 _)
    (f : pullback p q ⟶ Z) [Z.IsSeparated] (a : Spec (.of K) ⟶ Z)
    (h : Product.SectionFibers.productRightFiberInclusion p q y hy ≫ f = p ≫ a) :
    f = pullback.snd p q ≫ Product.SectionFibers.productLeftSection p q x hx ≫ f := by
  have : GeometricallyReduced p := ReducedFibers.smooth_geometricallyReduced p
  have : Flat p := inferInstance
  have : UniversallyOpen p := inferInstance
  exact Connected.ReducedCartesianRigidity.connectedReducedFamily_globalRigidity_of_cartesianFiber (pullback.snd p q)
    (pullback.snd p q).isOpenMap
    (Product.SectionFibers.productLeftSection p q x hx) (Product.SectionFibers.productLeftSection_snd p q x hx) f y a
    (Product.SectionFibers.productRightFiberInclusion p q y hy) p (Product.SectionFibers.productRightFiberInclusion_isPullback p q y hy) h

theorem smoothProperProductMap_eq_constant_of_axes (p : X ⟶ Spec (.of K)) (q : Y ⟶ Spec (.of K))
    [UniversallyClosed p] [Smooth p] [GeometricallyConnected p]
    [PreconnectedSpace Y] [IsReduced (pullback p q)]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    (y : Spec (.of K) ⟶ Y) (hy : y ≫ q = 𝟙 _)
    (f : pullback p q ⟶ Z) [Z.IsSeparated] (a : Spec (.of K) ⟶ Z)
    (hRight : Product.SectionFibers.productRightFiberInclusion p q y hy ≫ f = p ≫ a)
    (hLeft : Product.SectionFibers.productLeftSection p q x hx ≫ f = q ≫ a) :
    f = pullback.snd p q ≫ q ≫ a :=
  (smoothProperProductMap_rigidity p q x hx y hy f a hRight).trans
    (congrArg (fun k => pullback.snd p q ≫ k) hLeft)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProductRigidity
