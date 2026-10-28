import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PresentationPullback

/-! # Representative Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.RepresentativePullback

noncomputable section

/-! A genuine local representative of finite-coefficient H¹ pulls back
to a representative of the actual cohomological pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtalePullbackSections
open OAI.NumberTheory.PadicHodge.IntegralComparison.EtalePullbackGlobalSections.Pro OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PresentationPullback

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
  (I Q : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
  (i : AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y ⟶ I) (g : I ⟶ Q) (h : i ≫ g = 0)
  (hS : (PresentationPullback.source ℓ n I Q i g h).ShortExact)
  (U D : Y.ProEt) (a b : D ⟶ U) (V E : X.ProEt) (c d : E ⟶ V)
  (rU : V ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj U) (rD : E ⟶ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).obj D)
  (ha : rD ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map a = c ≫ rU)
  (hb : rD ≫ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtBaseChange f).map b = d ≫ rU)

def representative {x : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y).H 1}
    (r : CoverCharacter.Representative (PresentationPullback.source ℓ n I Q i g h) hS U D a b x) :
    CoverCharacter.Representative (PresentationPullback.complex ℓ n f I Q i g h) (PresentationPullback.shortExact ℓ n f I Q i g h hS) V E c d
      (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1 x) where
  z := EtalePullbackGlobalSections.Pro.globalMap f Q r.z
  t := ProEtalePullbackSections.sectionMap f I rU r.t
  c := (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f).hom.app (op E)
    (ProEtalePullbackSections.sectionMap f (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y) rD r.c)
  class_eq := (PresentationPullback.connecting ℓ n f I Q i g h hS r.z).trans
    (congrArg (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.finiteEllAdicPullback ℓ n f 1) r.class_eq)
  lift_eq := by
    change ((AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).map g).hom.app (op V) (ProEtalePullbackSections.sectionMap f I rU r.t) = _
    rw [ProEtalePullbackSections.naturality, r.lift_eq, EtalePullbackGlobalSections.Pro.local_global]
    rfl
  difference_eq := by
    have he := congrArg
      (fun α : (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y) ⟶
        (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtSheafPullback f).obj I => α.hom.app (op E)
          (ProEtalePullbackSections.sectionMap f (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y) rD r.c))
      (PresentationPullback.coefficient_comp_f ℓ n f I Q i g h)
    change (PresentationPullback.complex ℓ n f I Q i g h).f.hom.app (op E)
      ((AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f).hom.app (op E)
        (ProEtalePullbackSections.sectionMap f (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n Y) rD r.c)) = _ at he
    rw [he, ProEtalePullbackSections.naturality, r.difference_eq, map_sub, ProEtalePullbackSections.restrict_target, ProEtalePullbackSections.restrict_target, ha, hb,
      ← ProEtalePullbackSections.restrict_source, ← ProEtalePullbackSections.restrict_source]
    rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.RepresentativePullback
