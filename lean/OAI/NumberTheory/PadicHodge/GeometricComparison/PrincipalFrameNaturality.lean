import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameComplex

/-! # Principal Frame Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameNaturality.PrincipalFrameComparisonNaturality

noncomputable section

/-! The principal PD-to-ordinary comparison is natural in maps between
actual frame diagrams, including bounded-level reductions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] (r : B) (δ : DividedPowers (Ideal.span {r}))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
  {D : Type v} [Category.{w} D] (F G : D ⥤ (IntegralComparison.BigCrystallineSite.Object p B (Ideal.span {r}) δ f)ᵒᵖ)
  (hF : ∀ d, (F.obj d).unop.ideal = Ideal.span {(F.obj d).unop.base r})
  (hG : ∀ d, (G.obj d).unop.ideal = Ideal.span {(G.obj d).unop.base r})
  (a : F ⟶ G)

local instance objectAlgebra (O : IntegralComparison.BigCrystallineSite.Object p B (Ideal.span {r}) δ f) : Algebra B O.ring := O.base.toAlgebra

theorem natural : Functor.whiskerRight a (Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.functor f) ≫
    (PrincipalFrameComplex.PrincipalFrameComplexComparison.iso r δ f G hG).hom =
      (PrincipalFrameComplex.PrincipalFrameComplexComparison.iso r δ f F hF).hom ≫
        Functor.whiskerRight a (Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.functor f ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor B) := by
  apply NatTrans.ext
  funext d
  exact IntegralComparison.Principal.BaseNaturality.complexes r δ (hF d) (hG d)
    (F.obj d).unop.baseCompatible (G.obj d).unop.baseCompatible
    (CommAlgCat.ofHom (IntegralComparison.Crystalline.DeRham.ambientMap f (a.app d).unop)) (a.app d).unop.ringMap.isDPMorphism

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameNaturality.PrincipalFrameComparisonNaturality
