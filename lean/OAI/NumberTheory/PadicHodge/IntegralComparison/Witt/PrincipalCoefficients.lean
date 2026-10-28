import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Modules
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatCoefficientSheaves
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafUniverses
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientFlatness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.ExtAdjunction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.ExtIsomorphism
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientConstants

/-! # Principal Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.PrincipalCoefficients

noncomputable section

/-!
# IntegralComparison: exact integer restriction of the actual Witt coefficient sheaves

The actual principal-open sheaf categories have enough injectives. The
proved flatness of lifted Witt coefficients makes restriction to the
lifted integers exact and preserves injective objects.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Extension

universe u

abbrev IntegerRing (_k : Type u) := CoefficientFlatness.Integers.{u}

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]

local notation "Z" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.PrincipalCoefficients.IntegerRing k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.CoefficientFlatness.Coeff p k

variable {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of (WittVector p k))} (U : BigCrystallineSite.Object p (WittVector p k) J δ f)

abbrev IntegerSheaf := Sheaf (Principal.Topology.topology U.ring) (ModuleCat.{u + 1} Z)

instance integerHasSheafify : HasSheafify (Principal.Topology.topology U.ring) (ModuleCat.{u + 1} Z) :=
  Module.SheafUniverses.hasSheafify.{u + 1, u, u} (Principal.Topology.topology U.ring) Z

instance integerEnoughInjectives : EnoughInjectives (IntegerSheaf p k U) :=
  Module.SheafUniverses.enoughInjectives.{u + 1, u, u} (Principal.Topology.topology U.ring) Z

instance wittEnoughInjectives : EnoughInjectives (CrystallinePrincipal.Extension.PrincipalSheaf U) :=
  Module.SheafUniverses.enoughInjectives.{u + 1, u, u} (Principal.Topology.topology U.ring) R

abbrev extension : IntegerSheaf p k U ⥤ CrystallinePrincipal.Extension.PrincipalSheaf U :=
  FlatCoefficientSheaves.extension Z R (Principal.Topology.topology U.ring)

abbrev restriction : CrystallinePrincipal.Extension.PrincipalSheaf U ⥤ IntegerSheaf p k U :=
  FlatCoefficientSheaves.restriction Z R (Principal.Topology.topology U.ring)

def adjunction : extension p k U ⊣ restriction p k U :=
  FlatCoefficientSheaves.adjunction Z R (Principal.Topology.topology U.ring)

instance extension_preservesMonos : (extension p k U).PreservesMonomorphisms := by
  have := CoefficientFlatness.coefficient_algebra_flat p k
  exact FlatCoefficientSheaves.extension_preservesMonos Z R (Principal.Topology.topology U.ring)

instance restriction_preservesInjectives : (restriction p k U).PreservesInjectiveObjects := by
  have := CoefficientFlatness.coefficient_algebra_flat p k
  exact FlatCoefficientSheaves.restriction_preservesInjectives Z R (Principal.Topology.topology U.ring)

instance restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction p k U) := by
  infer_instance

instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction p k U) := by
  infer_instance

instance restriction_additive : (restriction p k U).Additive := by infer_instance

instance integerHasExt : HasExt.{u + 2} (IntegerSheaf p k U) := HasExt.standard _

/-- The exact coefficient adjunction acts on the actual higher Ext groups. -/
def extAdjunction (M : IntegerSheaf p k U) (N : CrystallinePrincipal.Extension.PrincipalSheaf U) (n : ℕ) :
    Abelian.Ext.{u + 2} ((extension p k U).obj M) N n ≃+
      Abelian.Ext.{u + 2} M ((restriction p k U).obj N) n :=
  Independent.ExtAdjunction.equivalence (restriction p k U) (adjunction p k U) M N n

abbrev integerConstantUnit : IntegerSheaf p k U :=
  (constantSheaf (Principal.Topology.topology U.ring) (ModuleCat.{u + 1} Z)).obj
    (ModuleCat.of Z Z)

def extensionConstantIso :
    (extension p k U).obj (integerConstantUnit p k U) ≅
      CrystallinePrincipal.Constant.Comparison.principalConstantUnit U :=
  CoefficientConstants.extensionConstantIso Z R (Principal.Topology.topology U.ring)

/-- Change coefficients in actual cohomology, including its constant source. -/
def constantExtEquiv (N : CrystallinePrincipal.Extension.PrincipalSheaf U) (n : ℕ) :
    Abelian.Ext.{u + 2} (CrystallinePrincipal.Constant.Comparison.principalConstantUnit U) N n ≃+
      Abelian.Ext.{u + 2} (integerConstantUnit p k U) ((restriction p k U).obj N) n :=
  (Independent.ExtIsomorphism.sourceEquiv (extensionConstantIso p k U).symm N n).trans
    (extAdjunction p k U (integerConstantUnit p k U) N n)

/-- The comparison applies to the original crystalline slice structure sheaf. -/
def sliceCohomologyEquiv (n : ℕ) :
    Crystalline.SliceStructure.Cohomology U n ≃+
      Abelian.Ext.{u + 2} (integerConstantUnit p k U)
        ((restriction p k U).obj (CrystallinePrincipal.Modules.zariskiUnitSheaf U)) n :=
  (CrystallinePrincipal.Modules.cohomologyEquiv U n).toAddEquiv.trans
    (constantExtEquiv p k U (CrystallinePrincipal.Modules.zariskiUnitSheaf U) n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.PrincipalCoefficients
