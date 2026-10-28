import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.ChartDeRham

/-! # Frame Complex Symbols -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FrameComplexSymbols

noncomputable section

/-! The actual principal-frame comparison preserves each differential
symbol in its original coefficient module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] (r : B) (δ : DividedPowers (Ideal.span {r}))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
  {D : Type v} [Category.{w} D] (F : D ⥤ (BigCrystallineSite.Object p B (Ideal.span {r}) δ f)ᵒᵖ)
  (h : ∀ d, (F.obj d).unop.ideal = Ideal.span {(F.obj d).unop.base r})

local instance objectAlgebra (d : D) : Algebra B (F.obj d).unop.ring := (F.obj d).unop.base.toAlgebra

theorem hom_symbol (d : D) (n : ℕ) (a : (F.obj d).unop.ring)
    (v : Fin n → (F.obj d).unop.ring) :
    ((GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison.iso r δ f F h).hom.app d).f n
        (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol B (F.obj d).unop.ring (F.obj d).unop.ideal
          (F.obj d).unop.dividedPowers a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol B (F.obj d).unop.ring a v :=
  Truncated.ChartDeRham.PrincipalBaseComplex.ofIdealEq_symbol B (F.obj d).unop.ring r δ
    (F.obj d).unop.ideal (F.obj d).unop.dividedPowers (h d)
    (F.obj d).unop.baseCompatible n a v

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FrameComplexSymbols
