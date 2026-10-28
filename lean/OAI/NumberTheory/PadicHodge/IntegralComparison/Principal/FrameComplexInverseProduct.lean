import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FrameComplexProduct

/-! # Frame Complex Inverse Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FrameComplexInverseProduct

noncomputable section

/-! The inverse of the actual principal-frame comparison preserves
integral de Rham products, on the original native form modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] (r : B) (δ : DividedPowers (Ideal.span {r}))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
  {D : Type v} [Category.{w} D] (F : D ⥤ (BigCrystallineSite.Object p B (Ideal.span {r}) δ f)ᵒᵖ)
  (h : ∀ d, (F.obj d).unop.ideal = Ideal.span {(F.obj d).unop.base r})

local instance inverseObjectAlgebra (d : D) : Algebra B (F.obj d).unop.ring := (F.obj d).unop.base.toAlgebra

theorem inv_wedge (d : D) (a b : ℕ)
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form B (F.obj d).unop.ring a)
    (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form B (F.obj d).unop.ring b) :
    ((GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison.iso r δ f F h).inv.app d).f (a+b)
      (IntegralDeRham.DeRhamWedge.wedge B (F.obj d).unop.ring a b x y) =
    RelativeFrame.Product.framePairing (F.obj d).unop a b
      (((GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison.iso r δ f F h).inv.app d).f a x)
      (((GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison.iso r δ f F h).inv.app d).f b y) :=
  BaseProduct.inv_wedge B (F.obj d).unop.ring r δ
    (F.obj d).unop.ideal (F.obj d).unop.dividedPowers (h d) (F.obj d).unop.baseCompatible a b x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FrameComplexInverseProduct
