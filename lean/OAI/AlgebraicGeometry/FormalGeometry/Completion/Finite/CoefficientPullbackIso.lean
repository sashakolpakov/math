import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientConstant
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence

/-! # Coefficient Pullback Iso -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullbackIso.Construction

noncomputable section

/-!
# Completion: the actual finite-coefficient inverse-image comparison is an isomorphism

The constant-sheaf comparison is compatible with the actual coefficient
functions under base change. Adjunction transports this compatibility to
the inverse-image comparison already used in finite cohomology pullback.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (ℓ n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Constants and actual finite-coefficient functions have the same direct-image comparison. -/
theorem finiteCoefficientConstantIso_pushforward :
    (CoefficientConstant.Construction.finiteCoefficientConstantIso ℓ n Y).hom ≫ CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n f =
      ConstantCoherence.Construction.proEtConstantToPushforward f (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))) ≫
        ((ProetalePullback.Construction.proEtBaseChange f).sheafPushforwardContinuous Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (CoefficientConstant.Construction.finiteCoefficientConstantIso ℓ n X).hom := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Y) Ab.{u + 1}).homEquiv _ _).injective
  change toSheafify (Scheme.ProEt.topology Y) (CoefficientConstant.Construction.finiteCoefficientConstantPresheaf ℓ n Y) ≫
      (CoefficientConstant.Construction.finiteCoefficientConstantIso ℓ n Y).hom.hom ≫
        (CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n f).hom =
    toSheafify (Scheme.ProEt.topology Y) (CoefficientConstant.Construction.finiteCoefficientConstantPresheaf ℓ n Y) ≫
      (ConstantCoherence.Construction.proEtConstantToPushforward f (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))).hom ≫
        Functor.whiskerLeft (ProetalePullback.Construction.proEtBaseChange f).op (CoefficientConstant.Construction.finiteCoefficientConstantIso ℓ n X).hom.hom
  rw [← Category.assoc, CoefficientConstant.Construction.finiteCoefficientConstantIso_unit,
    ← Category.assoc, ConstantCoherence.Construction.proEtConstantToPushforward_unit,
    ← Functor.whiskerLeft_comp, CoefficientConstant.Construction.finiteCoefficientConstantIso_unit]
  ext U a
  rfl

/-- The coefficient map used in actual cohomology pullback agrees with the constant comparison. -/
theorem finiteCoefficientConstantIso_pullback :
    (ProetalePullback.Construction.proEtSheafPullback f).map (CoefficientConstant.Construction.finiteCoefficientConstantIso ℓ n Y).hom ≫
        CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f =
      (ProetalePullback.Construction.proEtConstantPullbackIso f).hom.app
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))) ≫
        (CoefficientConstant.Construction.finiteCoefficientConstantIso ℓ n X).hom := by
  have h := ((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).homEquiv_naturality_right_square
      (CoefficientConstant.Construction.finiteCoefficientConstantIso ℓ n Y).hom (CoefficientPullback.Construction.proEtFiniteCoefficientToPushforward ℓ n f)
      (ConstantCoherence.Construction.proEtConstantToPushforward f (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n)))))
      (CoefficientConstant.Construction.finiteCoefficientConstantIso ℓ n X).hom (finiteCoefficientConstantIso_pushforward ℓ n f)
  rw [← ConstantCoherence.Construction.proEtConstantPullbackIso_adjoint, Equiv.symm_apply_apply] at h
  exact h

/-- Actual finite coefficients are preserved by inverse image along every scheme morphism. -/
instance proEtFiniteCoefficientPullback_isIso : IsIso (CoefficientPullback.Construction.proEtFiniteCoefficientPullback ℓ n f) := by
  rw [← isIso_comp_left_iff ((ProetalePullback.Construction.proEtSheafPullback f).map (CoefficientConstant.Construction.finiteCoefficientConstantIso ℓ n Y).hom),
    finiteCoefficientConstantIso_pullback]
  infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullbackIso.Construction
