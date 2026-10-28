import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Cocontinuous
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.KanExtensionUniverses

/-! # Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Extension

noncomputable section

/-!
# IntegralComparison: exact functors between crystalline slices and principal opens

Restriction is exact by continuity and cocontinuity. Its left adjoint
is exact by the proved flatness of the principal-open inclusion, so
restriction also preserves injective objects.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f)

abbrev Coeff := ULift.{u + 1} B

abbrev SliceSheaf := Sheaf (BigCrystallineSite.Object.topology.over U) (ModuleCat.{u + 1} (Coeff (B := B)))

abbrev PrincipalSheaf :=
  Sheaf (Principal.Topology.topology U.ring) (ModuleCat.{u + 1} (Coeff (B := B)))

instance principalHasSheafify : HasSheafify (Principal.Topology.topology U.ring)
    (ModuleCat.{u + 1} (Coeff (B := B))) := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget (ModuleCat.{u + 1} (Coeff (B := B)))) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  exact HasSheafify.mk' _ _ (plusPlusAdjunction (Principal.Topology.topology U.ring)
    (ModuleCat.{u + 1} (Coeff (B := B))))

abbrev restriction : SliceSheaf U ⥤ PrincipalSheaf U :=
  (CrystallinePrincipal.Functor.inclusion U).sheafPushforwardContinuous (ModuleCat.{u + 1} (Coeff (B := B)))
    (Principal.Topology.topology U.ring) (BigCrystallineSite.Object.topology.over U)

instance restriction_additive : (restriction U).Additive where
  map_add := by intros; rfl

instance restriction_linear : (restriction U).Linear (Coeff (B := B)) where
  map_smul := by intros; rfl

instance restriction_leftAdjoint : (restriction U).IsLeftAdjoint :=
  ((CrystallinePrincipal.Functor.inclusion U).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (Coeff (B := B)))
    (Principal.Topology.topology U.ring) (BigCrystallineSite.Object.topology.over U)).isLeftAdjoint

instance restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction U) := by infer_instance

instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction U) := by infer_instance

abbrev extension : PrincipalSheaf U ⥤ SliceSheaf U :=
  (CrystallinePrincipal.Functor.inclusion U).sheafPullback (ModuleCat.{u + 1} (Coeff (B := B)))
    (Principal.Topology.topology U.ring) (BigCrystallineSite.Object.topology.over U)

def adjunction : extension U ⊣ restriction U :=
  (CrystallinePrincipal.Functor.inclusion U).sheafAdjunctionContinuous (ModuleCat.{u + 1} (Coeff (B := B)))
    (Principal.Topology.topology U.ring) (BigCrystallineSite.Object.topology.over U)

instance extension_leftAdjoint : (extension U).IsLeftAdjoint := (adjunction U).isLeftAdjoint

instance extension_preservesFiniteLimits : PreservesFiniteLimits (extension U) := by
  have := Module.KanExtensionUniverses.preservesFiniteLimits (Coeff (B := B)) (CrystallinePrincipal.Functor.inclusion U)
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

instance extension_preservesFiniteColimits : PreservesFiniteColimits (extension U) := by infer_instance

instance extension_additive : (extension U).Additive := Functor.additive_of_preserves_binary_products _

instance restriction_preservesInjectives : (restriction U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (adjunction U)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Extension
