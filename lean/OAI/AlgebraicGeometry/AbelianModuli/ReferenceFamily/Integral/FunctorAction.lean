import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

/-! # Functor Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.FunctorAction

noncomputable section

/-! A ring action on the actual additive functor of points gives the
scheme endomorphisms and every equation in the ReferenceFamily integral action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

def integralActionOfFunctorAction {R : Type} [CommRing R] {S : Scheme.{0}} {g : ℕ}
    (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (r : R →+* AbelianScheme.TateComparison.End.IntegralEnd A.scheme) : ActionData.IntegralAction R A where
  map a := AbelianScheme.TateComparison.End.endSchemeMap A.scheme (r a)
  preservesGroup a := inferInstance
  map_zero := by rw [map_zero, AbelianScheme.TateComparison.BaseChange.endSchemeMap_zero]
  map_one := by rw [map_one, AbelianScheme.TateComparison.BaseChange.endSchemeMap_one]
  map_add a b := by rw [map_add, AbelianScheme.TateComparison.BaseChange.endSchemeMap_add]
  map_mul a b := by rw [map_mul, AbelianScheme.TateComparison.BaseChange.endSchemeMap_mul]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.FunctorAction
