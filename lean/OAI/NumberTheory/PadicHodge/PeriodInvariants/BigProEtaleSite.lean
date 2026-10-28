import OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlatModuleKanExtension
import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.SheafRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.Criterion

/-! # Big Pro Etale Site -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.BigProEtaleSite

noncomputable section

/-!
# Exact restriction on big and small pro-etale sites

The big site consists of all schemes over X. Its functors for arbitrary
base morphisms permit cohomological pullback. Restriction to the actual
small pro-etale site is exact and preserves injectives; at constant
coefficients the Ext comparison is therefore bijective in every degree.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology

variable (p : ℕ) [Fact p.Prime] (X : Scheme.{u})

abbrev BigSheaf := Sheaf (Scheme.proetaleTopology.over X) (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))
abbrev SmallSheaf := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))

instance bigHasExt : HasExt.{u + 2} (BigSheaf p X) := HasExt.standard _

instance bigGrothendieck : IsGrothendieckAbelian.{u + 1} (BigSheaf p X) := by
  let : SmallCategory (SmallModel.{u + 1} (Over X)) := smallCategorySmallModel.{u + 1, u, u + 1} (Over X)
  let e := equivSmallModel.{u + 1} (Over X)
  let T := e.inverse.inducedTopology (Scheme.proetaleTopology.over X)
  have : HasSheafify T (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) :=
    HasSheafify.mk' T (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))
      (plusPlusAdjunction.{u + 1, u + 1, u + 2, u + 1, u + 1, u + 1}
        T (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)))
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1, u + 1, u, u + 2, u + 1}
    (Scheme.proetaleTopology.over X) (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))

instance bigEnoughInjectives : EnoughInjectives (BigSheaf p X) := by infer_instance

omit p [Fact p.Prime] in
instance inclusion_cocontinuous : (Scheme.ProEt.forget X).IsCocontinuous
    (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X) := by
  let F := Scheme.ProEt.forget X
  let T := Scheme.proetaleTopology.over X
  have : F.IsContinuous (F.restrictedTopology T) T :=
    Functor.isContinuous_iff_coverPreserving.mpr (F.coverPreserving_restrictedTopology T)
  rw [Scheme.ProEt.topology_eq_inducedTopology, ← Functor.restrictedTopology_eq_inducedTopology]
  infer_instance

abbrev restriction : BigSheaf p X ⥤ SmallSheaf p X :=
  (Scheme.ProEt.forget X).sheafPushforwardContinuous (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))
    (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X)

instance restriction_additive : (restriction p X).Additive where
  map_add := by intros; rfl

instance restriction_linear : (restriction p X).Linear (IntegralComparison.Cohomology.Coeff.{u} p) where
  map_smul := by intros; rfl

instance restriction_leftAdjoint : (restriction p X).IsLeftAdjoint :=
  ((Scheme.ProEt.forget X).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))
    (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X)).isLeftAdjoint

instance restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction p X) := by infer_instance

instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction p X) := by infer_instance

abbrev extension : SmallSheaf p X ⥤ BigSheaf p X :=
  (Scheme.ProEt.forget X).sheafPullback (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))
    (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X)

instance extension_preservesFiniteLimits : PreservesFiniteLimits (extension p X) := by
  let : PreservesFiniteLimits ((Scheme.ProEt.forget X).op.lan :
      (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) ⥤
        (Over X)ᵒᵖ ⥤ ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) :=
    IntegralComparison.FlatModuleKanExtension.preservesFiniteLimits (IntegralComparison.Cohomology.Coeff.{u} p) (Scheme.ProEt.forget X)
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

instance restriction_preservesInjectives : (restriction p X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    ((Scheme.ProEt.forget X).sheafAdjunctionContinuous (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))
      (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X))

def constantUnit : BigSheaf p X :=
  (constantSheaf (Scheme.proetaleTopology.over X) (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))).obj
    (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p))

theorem mapExt_bijective (Y : BigSheaf p X) (n : ℕ) :
    Function.Bijective ((restriction p X).mapExtAddHom (constantUnit p X) Y n) := by
  apply IntegralComparison.Ext.Criterion.Comparison.bijective_of_hom_bijective
  intro Z
  exact IntegralComparison.Constant.SheafRestriction.map_bijective (Scheme.ProEt.forget X)
    (Scheme.ProEt.topology X) (Scheme.proetaleTopology.over X)
    (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p)) Z

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.BigProEtaleSite
