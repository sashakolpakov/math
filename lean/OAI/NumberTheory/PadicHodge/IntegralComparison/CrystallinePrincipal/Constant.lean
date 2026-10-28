import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Extension
import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.SheafRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.Criterion
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

/-! # Constant -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Constant.Comparison

noncomputable section

/-!
# IntegralComparison: actual cohomology comparison on a crystalline slice

Restriction to principal opens is bijective on Ext from the constant
coefficient sheaf. The proof uses the exact adjunction, enough injectives,
and the constant-source Hom comparison, with no cohomological hypothesis.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Extension

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f)

instance sliceGrothendieck : IsGrothendieckAbelian.{u + 1} (Extension.SliceSheaf U) := by
  let C := Over U
  let T := BigCrystallineSite.Object.topology.over U
  let R := Extension.Coeff (B := B)
  let : SmallCategory (SmallModel.{u + 1} C) := smallCategorySmallModel.{u + 1, u, u + 1} C
  let e := equivSmallModel.{u + 1} C
  let K := e.inverse.inducedTopology T
  have : HasSheafify K (ModuleCat.{u + 1} R) :=
    HasSheafify.mk' K (ModuleCat.{u + 1} R)
      (plusPlusAdjunction.{u + 1, u + 1, u + 2, u + 1, u + 1, u + 1} K (ModuleCat.{u + 1} R))
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    T (ModuleCat.{u + 1} R)

instance sliceEnoughInjectives : EnoughInjectives (Extension.SliceSheaf U) := by infer_instance

instance sliceHasExt : HasExt.{u + 2} (Extension.SliceSheaf U) := HasExt.standard _

instance principalHasExt : HasExt.{u + 2} (Extension.PrincipalSheaf U) := HasExt.standard _

abbrev constantUnit : Extension.SliceSheaf U :=
  (constantSheaf (BigCrystallineSite.Object.topology.over U) (ModuleCat.{u + 1} (Extension.Coeff (B := B)))).obj
    (ModuleCat.of (Extension.Coeff (B := B)) (Extension.Coeff (B := B)))

abbrev principalConstantUnit : Extension.PrincipalSheaf U :=
  (constantSheaf (Principal.Topology.topology U.ring) (ModuleCat.{u + 1} (Extension.Coeff (B := B)))).obj
    (ModuleCat.of (Extension.Coeff (B := B)) (Extension.Coeff (B := B)))

theorem mapExt_bijective (Y : Extension.SliceSheaf U) (n : ℕ) :
    Function.Bijective ((Extension.restriction U).mapExtAddHom (constantUnit U) Y n) := by
  apply IntegralComparison.Ext.Criterion.Comparison.bijective_of_hom_bijective
  intro Z
  exact Constant.SheafRestriction.map_bijective (CrystallinePrincipal.Functor.inclusion U)
    (Principal.Topology.topology U.ring) (BigCrystallineSite.Object.topology.over U)
    (ModuleCat.{u + 1} (Extension.Coeff (B := B)))
    (ModuleCat.of (Extension.Coeff (B := B)) (Extension.Coeff (B := B))) Z

def constantTransport : (Extension.restriction U).obj (constantUnit U) ≅ principalConstantUnit U :=
  ((CrystallinePrincipal.Functor.inclusion U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (Extension.Coeff (B := B))) (Principal.Topology.topology U.ring)
    (BigCrystallineSite.Object.topology.over U)).symm.app
      ((Functor.const _).obj (ModuleCat.of (Extension.Coeff (B := B)) (Extension.Coeff (B := B))))

def comparison (Y : Extension.SliceSheaf U) (n : ℕ) :
    Abelian.Ext.{u + 2} (constantUnit U) Y n →ₗ[Extension.Coeff (B := B)]
      Abelian.Ext.{u + 2} (principalConstantUnit U) ((Extension.restriction U).obj Y) n :=
  (Etale.Frobenius.extIsoCongr (Extension.Coeff (B := B)) (constantTransport U) (Iso.refl _) n).toLinearMap.comp
    ((Extension.restriction U).mapExtLinearMap (Extension.Coeff (B := B)) (constantUnit U) Y n)

theorem comparison_bijective (Y : Extension.SliceSheaf U) (n : ℕ) : Function.Bijective (comparison U Y n) :=
  (Etale.Frobenius.extIsoCongr (Extension.Coeff (B := B)) (constantTransport U) (Iso.refl _) n).bijective.comp
    (mapExt_bijective U Y n)

def cohomologyEquiv (Y : Extension.SliceSheaf U) (n : ℕ) :
    Abelian.Ext.{u + 2} (constantUnit U) Y n ≃ₗ[Extension.Coeff (B := B)]
      Abelian.Ext.{u + 2} (principalConstantUnit U) ((Extension.restriction U).obj Y) n :=
  LinearEquiv.ofBijective (comparison U Y n) (comparison_bijective U Y n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Constant.Comparison
