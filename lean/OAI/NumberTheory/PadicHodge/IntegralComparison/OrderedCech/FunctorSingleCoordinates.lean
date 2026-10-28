import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.RowTotalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CechSingle

/-! # Functor Single Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.FunctorSingleCoordinates

noncomputable section

/-! Functorial single-degree coordinates are the original ordered
Čech single-degree coordinates for the actual sheaf functor. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X S : Scheme.{u}} (π : X ⟶ S)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (M : X.Modules) (c : ℕ)

theorem homologyIso_eq (n : ℕ) :
    Functor.SingleTotal.homologyIso (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U) M c n =
      CechSingle.homologyIso π U M c n := by
  simp only [Functor.SingleTotal.homologyIso, CechSingle.homologyIso,
    Single.RowTotalCoordinates.homologyIso_eq]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.FunctorSingleCoordinates
