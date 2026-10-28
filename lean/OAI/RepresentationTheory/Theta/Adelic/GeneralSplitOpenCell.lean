import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitTensorAction

/-! # General Split Open Cell -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeneralSplitOpenCell

noncomputable section

/-! Actual units for the two open-cell differences in the stable split
tensor polarization. -/

open scoped Kronecker

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
open OAI.RepresentationTheory.Theta.Adelic.GeneralSplitTensorAction

variable {k : Type} [Field k] [CharZero k] {d : k}
variable (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0) (n m : ℕ)
variable (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)

theorem plus_tensor_units (g : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (h : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    SplitUnitary.plusUnits r hr hr0 (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits g h) = Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits (SplitUnitary.plusUnits r hr hr0 g) (SplitUnitary.plusUnits r hr hr0 h) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact map_mul (SpecialUnitary.SplitAlgebra.plus r hr hr0) (g.val i.1 j.1) (h.val i.2 j.2)

theorem linearPair_tensor (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) :
    GeneralSplitTensorAction.linearPair r hr hr0 n m H K g =
      GeneralSplitTensorAction.reindexUnit n m (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits (SplitUnitary.plusUnits r hr hr0 g.1.val) (SplitUnitary.plusUnits r hr hr0 g.2.val)) := by
  change GeneralSplitTensorAction.reindexUnit n m (SplitUnitary.plusUnits r hr hr0 (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits g.1.val g.2.val)) = _
  rw [plus_tensor_units]

def firstDifference (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k (n * m) :=
  GeneralSplitTensorAction.reindexUnit n m (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits (SplitUnitary.plusUnits r hr hr0 u) (1 : (Matrix (Fin m) (Fin m) k)ˣ))

def secondDifference (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k (n * m) :=
  GeneralSplitTensorAction.reindexUnit n m (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits (1 : (Matrix (Fin n) (Fin n) k)ˣ) (SplitUnitary.plusUnits r hr hr0 u))

theorem firstDifference_val (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val) (u : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (hu : u.val = g.val.val - 1) :
    (firstDifference r hr hr0 n m u).val = (GeneralSplitTensorAction.linearPair r hr hr0 n m H K (g, 1)).val - 1 := by
  rw [linearPair_tensor]
  have hp : SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 u.val = SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val - 1 := by
    rw [hu, map_sub, map_one]
  have ht : SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 u.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) k) =
      SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) k) - 1 := by
    rw [hp]
    calc
      _ = SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val ⊗ₖ (1 : Matrix (Fin m) (Fin m) k) -
          (1 : Matrix (Fin n) (Fin n) k) ⊗ₖ (1 : Matrix (Fin m) (Fin m) k) := by
        apply Matrix.ext
        intro i j
        exact sub_mul _ _ _
      _ = _ := by rw [Matrix.one_kronecker_one]
  have he := congrArg (Matrix.reindexRingEquiv k (finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m))) ht
  rw [map_sub, map_one] at he
  change (firstDifference r hr hr0 n m u).val =
    (GeneralSplitTensorAction.reindexUnit n m (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits (SplitUnitary.plusUnits r hr hr0 g.val) (SplitUnitary.plusUnits r hr hr0 1))).val - 1
  rw [map_one]
  exact he

theorem secondDifference_val (g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) (u : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (hu : u.val = g.val.val - 1) :
    (secondDifference r hr hr0 n m u).val = (GeneralSplitTensorAction.linearPair r hr hr0 n m H K (1, g)).val - 1 := by
  rw [linearPair_tensor]
  have hp : SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 u.val = SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val - 1 := by
    rw [hu, map_sub, map_one]
  have ht : (1 : Matrix (Fin n) (Fin n) k) ⊗ₖ SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 u.val =
      (1 : Matrix (Fin n) (Fin n) k) ⊗ₖ SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val - 1 := by
    rw [hp]
    calc
      _ = (1 : Matrix (Fin n) (Fin n) k) ⊗ₖ SpecialUnitary.SplitAlgebra.plusMatrix r hr hr0 g.val.val -
          (1 : Matrix (Fin n) (Fin n) k) ⊗ₖ (1 : Matrix (Fin m) (Fin m) k) := by
        apply Matrix.ext
        intro i j
        exact mul_sub _ _ _
      _ = _ := by rw [Matrix.one_kronecker_one]
  have he := congrArg (Matrix.reindexRingEquiv k (finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m))) ht
  rw [map_sub, map_one] at he
  change (secondDifference r hr hr0 n m u).val =
    (GeneralSplitTensorAction.reindexUnit n m (Weil.AdelicSplitting.UnitaryBase.Construction.tensorUnits (SplitUnitary.plusUnits r hr hr0 1) (SplitUnitary.plusUnits r hr hr0 g.val))).val - 1
  rw [map_one]
  exact he

end

end OAI.RepresentationTheory.Theta.Adelic.GeneralSplitOpenCell
