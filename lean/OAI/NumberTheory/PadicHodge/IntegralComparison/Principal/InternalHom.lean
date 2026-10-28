import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.LiteralHomEquiv
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientFunctor

/-! # Internal Hom -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InternalHom

noncomputable section

/-! Original internal-Hom sections on all principal opens identify
naturally with Hom from the fixed ambient affine section module.
Both restriction and source differentials are the literal native maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (M N : X.Modules) [M.IsQuasicoherent]

def iso : SectionPresheaf.modules U hU (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N) ≅
    HomCoefficientFunctor.homPresheaf Γ(X, U) (SectionPresheaf.modules U hU N)
      (ModuleCat.of Γ(X, U) Γ(M, U)) :=
  NatIso.ofComponents
    (fun r => (LiteralHomEquiv.equiv U hU r.unop.val M N).toModuleIso)
    (by
      intro r s a
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro q
      apply LinearMap.ext
      intro m
      change LiteralHomEquiv.equiv U hU s.unop.val M N
          ((ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N).presheaf.map (SectionPresheaf.arrow U hU a.unop).op q) m =
        N.presheaf.map (SectionPresheaf.arrow U hU a.unop).op
          (LiteralHomEquiv.equiv U hU r.unop.val M N q m)
      rw [LiteralHomEquiv.equiv_apply,
        LiteralHomEquiv.equiv_apply]
      have hres : M.presheaf.map (SectionPresheaf.inclusion U s.unop).op m =
          M.presheaf.map (SectionPresheaf.arrow U hU a.unop).op
            (M.presheaf.map (SectionPresheaf.inclusion U r.unop).op m) := by
        rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
        rfl
      rw [hres]
      exact Affine.HomEvaluation.restriction M N (SectionPresheaf.openSubset U r.unop)
        (SectionPresheaf.arrow U hU a.unop) q (M.presheaf.map (SectionPresheaf.inclusion U r.unop).op m))

theorem hom_apply (r : (SectionPresheaf.Index U)ᵒᵖ)
    (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, SectionPresheaf.openSubset U r.unop)) (m : Γ(M, U)) :
    (show Γ(M, U) →ₗ[Γ(X, U)] Γ(N, SectionPresheaf.openSubset U r.unop) from
      (iso U hU M N).hom.app r q) m =
      Affine.HomEvaluation.evaluation M N (SectionPresheaf.openSubset U r.unop) q
        (M.presheaf.map (SectionPresheaf.inclusion U r.unop).op m) :=
  LiteralHomEquiv.equiv_apply U hU r.unop.val M N q m

theorem precomp {M' : X.Modules} [M'.IsQuasicoherent] (f : M ⟶ M') :
    SectionPresheaf.moduleHom U hU (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap f (𝟙 N)) ≫ (iso U hU M N).hom =
      (iso U hU M' N).hom ≫ HomCoefficientFunctor.precomp Γ(X, U)
        (SectionPresheaf.modules U hU N) (f.val.app (op U)) := by
  apply NatTrans.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro m
  exact LiteralHomEquiv.precomp U hU r.unop.val M N f q m

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.InternalHom
