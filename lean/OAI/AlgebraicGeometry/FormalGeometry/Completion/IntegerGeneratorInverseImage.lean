import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegerGeneratorPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackForgetAdjunction

/-! # Integer Generator Inverse Image -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegerGeneratorInverseImage.Construction

noncomputable section

/-!
# Completion: inverse image preserves the actual integer-generator section

This is the compatibility required for the finite-limit description of the
torsor of a pulled-back extension.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The integer constant comparison on the underlying sheaves of sets. -/
def proEtIntegerPullbackUnderlyingIso :
    (ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f).obj
      ((sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1})).obj (ProetalePullback.Construction.proEtIntegerConstant Y)) ≅
    (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj (ProetalePullback.Construction.proEtIntegerConstant X) :=
  ((ProEtale.PullbackTypes.Construction.proEtPullbackForgetIso f).app (ProetalePullback.Construction.proEtIntegerConstant Y)).symm ≪≫
    (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).mapIso
      ((ProetalePullback.Construction.proEtConstantPullbackIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The exact inverse image of the generator is the same chosen generator. -/
theorem proEtIntegerGeneratorMap_pullback :
    (ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f).map (FiniteTorsor.FiberPullback.Construction.proEtIntegerGeneratorMap Y) ≫
      (proEtIntegerPullbackUnderlyingIso f).hom =
    terminal.from ((ProEtale.PullbackTypes.Construction.proEtTypeSheafPullback f).obj
      (⊤_ (Sheaf (Scheme.ProEt.topology Y) (Type (u + 1))))) ≫ FiniteTorsor.FiberPullback.Construction.proEtIntegerGeneratorMap X := by
  let a := (ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  apply (a.homEquiv _ _).injective
  erw [a.homEquiv_naturality_left]
  change FiniteTorsor.FiberPullback.Construction.proEtIntegerGeneratorMap Y ≫
    a.homEquiv _ _ ((ProEtale.PullbackTypes.Construction.proEtPullbackForgetIso f).inv.app (ProetalePullback.Construction.proEtIntegerConstant Y) ≫
      (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).map
        ((ProetalePullback.Construction.proEtConstantPullbackIso f).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) = _
  rw [ProEtale.PullbackForgetAdjunction.Construction.proEtPullbackForgetIso_adjoint, ConstantCoherence.Construction.proEtConstantPullbackIso_adjoint,
    Adjunction.homEquiv_unit]
  ext U s
  exact IntegerGeneratorPullback.Construction.proEtConstantToPushforward_integerGenerator f U.unop

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegerGeneratorInverseImage.Construction
