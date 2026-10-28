import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.End

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange

noncomputable section

/-!
Base change of the actual algebraic endomorphism ring. This is needed to
transport the integral O_E action in a PEL family to correspondence covers
and geometric fibers. No compatibility with Hecke operators is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S T : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]

@[simp]
theorem endSchemeMap_zero : End.endSchemeMap A (0 : End.IntegralEnd A) = 1 := rfl

@[simp]
theorem endSchemeMap_one : End.endSchemeMap A (1 : End.IntegralEnd A) = 𝟙 A := rfl

theorem endSchemeMap_add (f g : End.IntegralEnd A) :
    End.endSchemeMap A (f + g) = End.endSchemeMap A f * End.endSchemeMap A g := rfl

/-- Endomorphism-ring multiplication is ordinary functional composition. -/
theorem endSchemeMap_mul (f g : End.IntegralEnd A) :
    End.endSchemeMap A (f * g) = End.endSchemeMap A g ≫ End.endSchemeMap A f := by
  exact End.endSchemeMap_points A f A (End.endSchemeMap A g)

/-- The canonical base-changed commutative group object. -/
abbrev baseChangedGroup (f : T ⟶ S) : CommGrp (Over T) :=
  CommGrp.mk ((Over.pullback f).obj A)

/-- Base change of actual algebraic endomorphisms, with all ring laws proved. -/
def endBaseChange (f : T ⟶ S) :
    End.IntegralEnd A →+* End.IntegralEnd (baseChangedGroup A f).X where
  toFun e := End.endOfSchemeMap (baseChangedGroup A f).X
    ((Over.pullback f).map (End.endSchemeMap A e))
  map_zero' := by
    apply End.endSchemeMap_injective (baseChangedGroup A f).X
    rw [End.endSchemeMap_ofSchemeMap, endSchemeMap_zero, endSchemeMap_zero]
    exact (Over.pullback f).map_one
  map_one' := by
    apply End.endSchemeMap_injective (baseChangedGroup A f).X
    rw [End.endSchemeMap_ofSchemeMap, endSchemeMap_one, endSchemeMap_one]
    exact (Over.pullback f).map_id A
  map_add' e d := by
    apply End.endSchemeMap_injective (baseChangedGroup A f).X
    rw [End.endSchemeMap_ofSchemeMap, endSchemeMap_add, endSchemeMap_add,
      End.endSchemeMap_ofSchemeMap, End.endSchemeMap_ofSchemeMap]
    exact (Over.pullback f).map_mul _ _
  map_mul' e d := by
    apply End.endSchemeMap_injective (baseChangedGroup A f).X
    rw [End.endSchemeMap_ofSchemeMap, endSchemeMap_mul, endSchemeMap_mul,
      End.endSchemeMap_ofSchemeMap, End.endSchemeMap_ofSchemeMap]
    exact (Over.pullback f).map_comp _ _

@[simp]
theorem endBaseChange_schemeMap (f : T ⟶ S) (e : End.IntegralEnd A) :
    End.endSchemeMap (baseChangedGroup A f).X (endBaseChange A f e) =
      (Over.pullback f).map (End.endSchemeMap A e) :=
  End.endSchemeMap_ofSchemeMap _ _

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.BaseChange
