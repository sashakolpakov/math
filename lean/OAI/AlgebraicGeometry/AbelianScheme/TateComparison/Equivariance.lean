import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateAction
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedComposites

/-! # Equivariance -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! PEL isogenies intertwine the actual integral Tate action and its
completion. These are consequences of the given algebraic equivariance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u
variable {R : Type u} [CommRing R] {S : Scheme.{u}} {g N n : ℕ}
  {P Q : PEL.PELFamilyData R g N S} (T : Over S) (q : ℕ) [Fact q.Prime]
  (e : PELIsogenies.PELIsogeny P Q n)

theorem PELIsogenies.PELIsogeny.tateIntegralAction_commute (r : R) :
    (Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom).comp (TateAction.tateIntegralAction T q P r) =
      (TateAction.tateIntegralAction T q Q r).comp (Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom) := by
  change (Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom).comp
      (TateAction.tateEndMap P.abelian.scheme T q (P.action r)) =
    (TateAction.tateEndMap Q.abelian.scheme T q (Q.action r)).comp
      (Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom)
  rw [TateAction.tateEndMap_eq_schemeTateMap, TateAction.tateEndMap_eq_schemeTateMap,
    ← Functor.schemeTateMap_comp, ← Functor.schemeTateMap_comp]
  exact PolarizedComposites.schemeTateMap_congr T q _ _ (e.equivariant r)

theorem PELIsogenies.PELIsogeny.tateCompletedAction_commute (z : ℤ_[q] ⊗[ℤ] R) :
    (Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom).comp (TateAction.tateCompletedAction T q P z) =
      (TateAction.tateCompletedAction T q Q z).comp (Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom) := by
  induction z using TensorProduct.inductionOn with
  | tmul a r =>
    rw [TateAction.tateCompletedAction_tmul, TateAction.tateCompletedAction_tmul, LinearMap.comp_smul,
      LinearMap.smul_comp, e.tateIntegralAction_commute T q r]
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
