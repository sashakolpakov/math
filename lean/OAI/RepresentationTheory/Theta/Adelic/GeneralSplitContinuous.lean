import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitCharacter
import OAI.RepresentationTheory.Theta.Adelic.GeneralSplitTensorAction
import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary

/-! # General Split Continuous -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeneralSplitContinuous

noncomputable section

/-! Continuity of the explicit split pair action and of the two
determinant characters, in the native quadratic-coefficient topology. -/

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra
open OAI.RepresentationTheory.Theta.Adelic.SplitNorm OAI.RepresentationTheory.Theta.Adelic.SplitUnitary OAI.RepresentationTheory.Theta.Adelic.GeneralSplitCharacter OAI.RepresentationTheory.Theta.Adelic.GeneralSplitTensorAction

variable {k : Type} [NormedField k] [CharZero k] {d : k}
variable (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)

theorem splitSection_continuous : Continuous (GeneralSplitCharacter.splitSection r hr hr0) := by
  apply Units.continuous_iff.mpr
  constructor
  · rw [Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
    constructor
    · change Continuous (fun a : kˣ => (a.val + 1) / 2)
      fun_prop
    · change Continuous (fun a : kˣ => (a.val - 1) / (2 * r))
      fun_prop
  · rw [Weil.AdelicSplitting.QuadraticTopology.Construction.quadratic_continuous_iff]
    constructor
    · change Continuous (fun a : kˣ => (a.inv + 1) / 2)
      fun_prop
    · change Continuous (fun a : kˣ => (a.inv - 1) / (2 * r))
      fun_prop

variable {I : Type} [Fintype I] [DecidableEq I]

theorem plusUnitary_continuous (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ) :
    Continuous (SplitUnitary.plusUnitary r hr hr0 Q) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro i <;> apply continuous_pi <;> intro j
  · exact (SplitUnitary.Continuous.plus_continuous r hr hr0).comp
      ((continuous_apply j).comp ((continuous_apply i).comp
        ((Units.continuous_val (M := Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))).comp continuous_subtype_val)))
  · exact (SplitUnitary.Continuous.plus_continuous r hr hr0).comp
      ((continuous_apply j).comp ((continuous_apply i).comp
        ((Units.continuous_coe_inv (M := Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))).comp continuous_subtype_val)))

omit [CharZero k] in
theorem determinant_continuous : Continuous (Matrix.GeneralLinearGroup.det : (Matrix I I k)ˣ → kˣ) := by
  apply Units.continuous_iff.mpr
  exact ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩

def continuousUnitaryCharacter (Q : (Matrix I I (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
    (χ : (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)ˣ →ₜ* Circle) : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary Q.val →ₜ* Circle :=
  { GeneralSplitCharacter.unitaryCharacter r hr hr0 Q χ.toMonoidHom with
    continuous_toFun := χ.continuous.comp ((splitSection_continuous r hr hr0).comp
      (determinant_continuous.comp (plusUnitary_continuous r hr hr0 Q))) }

variable (n m : ℕ) (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)
variable (K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ)

theorem linearPair_continuous : Continuous (GeneralSplitTensorAction.linearPair r hr hr0 n m H K) := by
  apply Units.continuous_iff.mpr
  constructor <;> apply continuous_pi <;> intro i <;> apply continuous_pi <;> intro j
  · change Continuous (fun g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val =>
      SpecialUnitary.SplitAlgebra.plus r hr hr0 (g.1.val.val (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
        g.2.val.val (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2))
    apply (SplitUnitary.Continuous.plus_continuous r hr hr0).comp
    fun_prop
  · change Continuous (fun g : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val =>
      SpecialUnitary.SplitAlgebra.plus r hr hr0 (g.1.val.inv (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
        g.2.val.inv (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2))
    apply (SplitUnitary.Continuous.plus_continuous r hr hr0).comp
    fun_prop

def continuousLinearPair : (Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H.val × Weil.AdelicSplitting.UnitaryBase.Construction.Unitary K.val) →ₜ* Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k (n * m) :=
  { GeneralSplitTensorAction.linearPair r hr hr0 n m H K with continuous_toFun := linearPair_continuous r hr hr0 n m H K }

end

end OAI.RepresentationTheory.Theta.Adelic.GeneralSplitContinuous
