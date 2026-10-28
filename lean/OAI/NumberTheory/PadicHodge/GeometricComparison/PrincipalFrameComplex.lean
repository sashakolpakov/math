import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseNaturality

/-! # Principal Frame Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison

noncomputable section

/-! A diagram of actual crystalline frames with principal base-generated
ideals has a natural PD-to-ordinary de Rham comparison isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] (r : B) (δ : DividedPowers (Ideal.span {r}))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
  {D : Type v} [Category.{w} D] (F : D ⥤ (IntegralComparison.BigCrystallineSite.Object p B (Ideal.span {r}) δ f)ᵒᵖ)
  (h : ∀ d, (F.obj d).unop.ideal = Ideal.span {(F.obj d).unop.base r})

local instance objectAlgebra (d : D) : Algebra B (F.obj d).unop.ring := (F.obj d).unop.base.toAlgebra

def iso : F ⋙ Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor f ≅
    F ⋙ Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.functor f ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor B :=
  NatIso.ofComponents
    (fun d => IntegralComparison.Principal.BaseComplex.ofIdealEq B (F.obj d).unop.ring r δ
      (F.obj d).unop.ideal (F.obj d).unop.dividedPowers (h d) (F.obj d).unop.baseCompatible)
    (fun {_ _} α => IntegralComparison.Principal.BaseNaturality.complexes r δ (h _) (h _)
      (F.obj _).unop.baseCompatible (F.obj _).unop.baseCompatible
      (CommAlgCat.ofHom (IntegralComparison.Crystalline.DeRham.ambientMap f (F.map α).unop))
      (F.map α).unop.ringMap.isDPMorphism)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameComplex.PrincipalFrameComplexComparison
