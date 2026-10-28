import OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeMate
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InvariantRestriction
import OAI.AlgebraicGeometry.Picard.PoincareBundle.BeckDescent

/-! # Module Descent Base Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleDescentBaseChange

noncomputable section

/-!
# Flat base change of full module descent data for PoincareBundle

The canonical tensor-square mate transports a coaction with its counit
and cocycle. Flat base change also commutes with the explicit invariant
equalizer used to construct the descended module.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

open OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleBaseChangeMate

/-- The square of extension-of-scalars functors obtained from the
commutative square of restriction functors. -/
def extensionSquareIso :
    ModuleCat.extendScalars.{u, u, u} (algebraMap R T) ⋙ ModuleCat.extendScalars.{u, u, u} (ModuleBaseChangeMate.rightMap R S T) ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap R S) ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap S (S ⊗[R] T)) :=
  (conjugateIsoEquiv
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S)).comp
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap S (S ⊗[R] T))))
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R T)).comp
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (ModuleBaseChangeMate.rightMap R S T)))).symm
    (ModuleBaseChangeMate.restrictionSquareIso R S T)

/-- Its right mate is the canonical, already proved invertible, base-change map. -/
theorem rightMate_eq :
    DescentRestriction.rightMate
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S))
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (ModuleBaseChangeMate.rightMap R S T))
      (extensionSquareIso R S T) = ModuleBaseChangeMate.baseChangeMap R S T := by
  let γ := TwoSquare.mk _ _ _ _ (ModuleBaseChangeMate.restrictionSquareIso R S T).hom
  have h := iterated_mateEquiv_conjugateEquiv_symm
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S))
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (ModuleBaseChangeMate.rightMap R S T))
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R T))
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap S (S ⊗[R] T))) γ
  apply congrArg TwoSquare.natTrans
  apply (mateEquiv (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S))
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (ModuleBaseChangeMate.rightMap R S T))).symm.injective
  change (mateEquiv (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S))
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (ModuleBaseChangeMate.rightMap R S T))).symm
      ((mateEquiv (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S))
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (ModuleBaseChangeMate.rightMap R S T)))
          (TwoSquare.mk _ _ _ _ (extensionSquareIso R S T).hom)) = _
  rw [Equiv.symm_apply_apply]
  exact h.symm

theorem rightMate_isIso :
    IsIso (DescentRestriction.rightMate
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S))
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (ModuleBaseChangeMate.rightMap R S T))
      (extensionSquareIso R S T)) := by
  exact (rightMate_eq R S T).symm ▸ ModuleBaseChangeMate.baseChangeMap_isIso R S T

/-- Base change of full algebraic descent data, including its coaction laws. -/
def baseChangeDatum : Affine.Descent.ModuleDatum.{u, u} (algebraMap R S) ⥤
    Affine.Descent.ModuleDatum.{u, u} (ModuleBaseChangeMate.rightMap R S T) :=
  DescentRestriction.coalgebraRestriction
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S))
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (ModuleBaseChangeMate.rightMap R S T)) (extensionSquareIso R S T)

/-- The underlying module is ordinary extension to the tensor ring. -/
theorem baseChangeDatum_obj_A (D : Affine.Descent.ModuleDatum.{u, u} (algebraMap R S)) :
    ((baseChangeDatum R S T).obj D).A =
      (ModuleCat.extendScalars.{u, u, u} (algebraMap S (S ⊗[R] T))).obj D.A := rfl

/-- Flat base change commutes with the actual module of invariants. -/
def invariantsBaseChangeIso (hT : (algebraMap R T).Flat)
    (D : Affine.Descent.ModuleDatum.{u, u} (algebraMap R S)) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R T)).obj
      (BeckDescent.moduleInvariants (algebraMap R S) D) ≅
        BeckDescent.moduleInvariants (ModuleBaseChangeMate.rightMap R S T) ((baseChangeDatum R S T).obj D) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hT
  have := rightMate_isIso R S T
  exact InvariantRestriction.invariantRestrictionIso
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap R S))
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (ModuleBaseChangeMate.rightMap R S T)) (extensionSquareIso R S T) D

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ModuleDescentBaseChange
