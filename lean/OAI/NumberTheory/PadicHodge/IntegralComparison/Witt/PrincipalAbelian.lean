import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.PrincipalCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.ExtIsomorphism
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheaves
import OAI.NumberTheory.PadicHodge.IntegralComparison.AbelianSheafUniverses

/-! # Principal Abelian -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.PrincipalAbelian.Comparison

noncomputable section

/-!
# IntegralComparison: original crystalline slice cohomology as actual abelian sheaf Ext

The comparison retains the original structure sheaf, its principal-open
sections, and its exact coefficient universe. Flat Witt restriction and
the integer-module equivalence identify the higher Ext groups.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Extension

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of (WittVector p k))} (U : BigCrystallineSite.Object p (WittVector p k) J δ f)

abbrev AbelianSheaf := Sheaf (Principal.Topology.topology U.ring) AddCommGrpCat.{u + 1}

instance abelianHasSheafify : HasSheafify (Principal.Topology.topology U.ring) AddCommGrpCat.{u + 1} :=
  AbelianSheafUniverses.hasSheafify.{u + 1, u, u} (Principal.Topology.topology U.ring)

instance abelianEnoughInjectives : EnoughInjectives (AbelianSheaf p k U) :=
  AbelianSheafUniverses.enoughInjectives.{u + 1, u, u} (Principal.Topology.topology U.ring)

instance abelianHasExt : HasExt.{u + 2} (AbelianSheaf p k U) := HasExt.standard _

abbrev forgetCoefficients : CrystallinePrincipal.Extension.PrincipalSheaf U ⥤ AbelianSheaf p k U :=
  PrincipalCoefficients.restriction p k U ⋙
    Lifted.IntegerSheaves.sheafForget (Principal.Topology.topology U.ring)

abbrev constantUnit : AbelianSheaf p k U :=
  (constantSheaf (Principal.Topology.topology U.ring) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

def constantExtEquiv (N : CrystallinePrincipal.Extension.PrincipalSheaf U) (n : ℕ) :
    Abelian.Ext.{u + 2} (CrystallinePrincipal.Constant.Comparison.principalConstantUnit U) N n ≃+
      Abelian.Ext.{u + 2} (constantUnit p k U) ((forgetCoefficients p k U).obj N) n :=
  (PrincipalCoefficients.constantExtEquiv p k U N n).trans
    (Lifted.IntegerSheaves.extEquiv (Principal.Topology.topology U.ring)
      (PrincipalCoefficients.integerConstantUnit p k U)
      ((PrincipalCoefficients.restriction p k U).obj N) n) |>.trans
    (Independent.ExtIsomorphism.sourceEquiv
      (Lifted.IntegerSheaves.constantUnitIso (Principal.Topology.topology U.ring))
      ((forgetCoefficients p k U).obj N) n)

def sliceCohomologyEquiv (n : ℕ) :
    Crystalline.SliceStructure.Cohomology U n ≃+
      Abelian.Ext.{u + 2} (constantUnit p k U)
        ((forgetCoefficients p k U).obj (CrystallinePrincipal.Modules.zariskiUnitSheaf U)) n :=
  (CrystallinePrincipal.Modules.cohomologyEquiv U n).toAddEquiv.trans
    (constantExtEquiv p k U (CrystallinePrincipal.Modules.zariskiUnitSheaf U) n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.PrincipalAbelian.Comparison
