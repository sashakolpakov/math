import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.TorsorSheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Fiber Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: the actual torsor sheaf as a categorical fiber

The sheaf of lifts of the integer generator is the pullback of the middle
term along the generator section. This gives the finite-limit description
needed to commute torsors with exact inverse image.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The integer generator viewed as a morphism from the terminal sheaf of sets. -/
def FiberPullback.Construction.proEtIntegerGeneratorMap (X : Scheme.{u}) :
    ⊤_ (Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) ⟶
      (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj (ProetalePullback.Construction.proEtIntegerConstant X) where
  hom := {
    app U := ↾fun _ => App.Construction.proEtIntegerLocalGenerator X U.unop
    naturality U V g := by
      ext s
      exact (App.Construction.proEtIntegerLocalGenerator_naturality X g.unop).symm }

variable {X : Scheme.{u}} {ℓ n : ℕ} (E : App.Construction.FiniteCoefficientExtension ℓ n X)

/-- Forgetting the fiber condition gives a morphism of actual sheaves of sets. -/
def App.Construction.FiniteCoefficientExtension.fiberInclusion : E.fiberSheaf ⟶
    (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj E.middle where
  hom := { app U := ↾Subtype.val }

/-- The pullback square defining the actual torsor sheaf commutes. -/
theorem App.Construction.FiniteCoefficientExtension.fiberInclusion_projection :
    E.fiberInclusion ≫ (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).map E.projection =
      terminal.from E.fiberSheaf ≫ FiberPullback.Construction.proEtIntegerGeneratorMap X := by
  ext U s
  exact s.property

/-- The universal lift into the fiber is given by the actual pointwise fiber condition. -/
def App.Construction.FiniteCoefficientExtension.fiberPullbackLift
    (c : PullbackCone ((sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).map E.projection)
      (FiberPullback.Construction.proEtIntegerGeneratorMap X)) : c.pt ⟶ E.fiberSheaf where
  hom := {
    app U := ↾fun s => ⟨c.fst.hom.app U s, by
      exact congrArg (fun k : c.pt ⟶
        (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj (ProetalePullback.Construction.proEtIntegerConstant X) =>
          k.hom.app U s) c.condition⟩
    naturality U V g := by
      ext s
      apply Subtype.ext
      exact NatTrans.naturality_apply c.fst.hom g s }

/-- The original torsor is the categorical pullback over the integer generator. -/
theorem App.Construction.FiniteCoefficientExtension.fiberSheaf_isPullback :
    IsPullback E.fiberInclusion (terminal.from E.fiberSheaf)
      ((sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).map E.projection)
      (FiberPullback.Construction.proEtIntegerGeneratorMap X) := by
  apply IsPullback.of_isLimit' ⟨E.fiberInclusion_projection⟩
  refine PullbackCone.IsLimit.mk _ E.fiberPullbackLift ?_ ?_ ?_
  · intro c
    ext U s
    rfl
  · intro c
    exact terminalIsTerminal.hom_ext _ _
  · intro c m hm _
    ext U s
    apply Subtype.ext
    exact congrArg (fun k : c.pt ⟶
      (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj E.middle =>
        k.hom.app U s) hm

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
