import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingPullback

/-! # Principal Frame Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameSquare.PrincipalGeometricFrameSquare

noncomputable section

/-! The original principal PD-to-ordinary comparison commutes with a
geometric frame map over any compatible morphism of schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] (r : B) (δ : DividedPowers (Ideal.span {r}))
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)
  (P : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {r}) (δ := δ) fX n)
  (Q : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {r}) (δ := δ) fY n)
  (a : (IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj P ⟶ Q)
  (hP : P.obj.ideal = Ideal.span {P.obj.base r})
  (hQ : Q.obj.ideal = Ideal.span {Q.obj.base r})

local instance sourceAlgebra : Algebra B P.obj.ring := P.obj.base.toAlgebra
local instance targetAlgebra : Algebra B Q.obj.ring := Q.obj.base.toAlgebra

theorem square : (Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded fY n).map a.op ≫
    (IntegralComparison.Principal.BaseComplex.ofIdealEq B P.obj.ring r δ P.obj.ideal P.obj.dividedPowers hP P.obj.baseCompatible).hom =
    (IntegralComparison.Principal.BaseComplex.ofIdealEq B Q.obj.ring r δ Q.obj.ideal Q.obj.dividedPowers hQ Q.obj.baseCompatible).hom ≫
      (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor B).map ((Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.bounded fY n).map a.op) :=
  IntegralComparison.Principal.BaseNaturality.complexes r δ hQ hP Q.obj.baseCompatible P.obj.baseCompatible
    (CommAlgCat.ofHom (IntegralComparison.Crystalline.DeRham.ambientMap fY a.hom)) a.hom.ringMap.isDPMorphism

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameSquare.PrincipalGeometricFrameSquare
