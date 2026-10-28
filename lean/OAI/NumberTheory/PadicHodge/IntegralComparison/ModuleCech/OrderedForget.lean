import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.OrderedCoverCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.OrdinaryCoefficientProjection

/-! # Ordered Forget -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.OrderedForget

noncomputable section

/-! The original module Cech forgetful isomorphism preserves the
literal projection onto the ordered coefficient complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (M : X.left.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.left.Opens) (q : ℕ)

theorem comparison :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
      (Module.OrderedCoverCoordinates.projection R X M U q) ≫
      (Ordered.SingleGlobalSourceCoefficients.coefficientIso
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
        ((Affine.HomologyPresheaf.functor R X).obj M) U q).hom =
    (CohomologyNaturality.forgetHomologyIso R X U M q).hom ≫
      homologyMap (OrderedCech.Projection.map U M.presheaf) q :=
  OrderedCech.OrdinaryCoefficientProjection.Ordinary.homology U
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    ((Affine.HomologyPresheaf.functor R X).obj M) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.OrderedForget
