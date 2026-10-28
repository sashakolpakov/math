import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.Product

/-! # Frame Complex Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FrameComplexProduct

noncomputable section

/-! A diagram of genuine principal-base crystalline frames has a
multiplicative ordinary de Rham comparison in its original components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] (r : B) (δ : DividedPowers (Ideal.span {r}))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
  {D : Type v} [Category.{w} D] (F : D ⥤ (BigCrystallineSite.Object p B (Ideal.span {r}) δ f)ᵒᵖ)
  (h : ∀ d, (F.obj d).unop.ideal = Ideal.span {(F.obj d).unop.base r})

local instance objectAlgebra (d : D) : Algebra B (F.obj d).unop.ring := (F.obj d).unop.base.toAlgebra

theorem hom_wedge (d : D) (a b : ℕ)
    (x : RelativeFrame.FormMap.frameModule (F.obj d).unop a)
    (y : RelativeFrame.FormMap.frameModule (F.obj d).unop b) :
    ((GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison.iso r δ f F h).hom.app d).f (a+b)
      (RelativeFrame.Product.framePairing (F.obj d).unop a b x y) =
    IntegralDeRham.DeRhamWedge.wedge B (F.obj d).unop.ring a b
      (((GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison.iso r δ f F h).hom.app d).f a x)
      (((GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison.iso r δ f F h).hom.app d).f b y) :=
  BaseProduct.hom_wedge B (F.obj d).unop.ring r δ
    (F.obj d).unop.ideal (F.obj d).unop.dividedPowers (h d) (F.obj d).unop.baseCompatible a b x y

theorem hom_unit (d : D) :
    ((GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison.iso r δ f F h).hom.app d).f 0
      (PD.DeRhamWedgeAlgebra.unitForm B (F.obj d).unop.ring
        (F.obj d).unop.ideal (F.obj d).unop.dividedPowers) =
    IntegralDeRham.WedgeAlgebra.unitForm B (F.obj d).unop.ring :=
  BaseProduct.hom_unit B (F.obj d).unop.ring r δ
    (F.obj d).unop.ideal (F.obj d).unop.dividedPowers (h d) (F.obj d).unop.baseCompatible

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FrameComplexProduct
