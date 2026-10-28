import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FiniteModel
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # De Rham Coefficient Finiteness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.DeRhamCoefficientFiniteness

noncomputable section

/-! The original Witt coefficient functor and both universe lifts preserve finite residue-field modules. -/

open _root_.CategoryTheory Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]

def carrierEquiv (M : ModuleCat.{u} k) :
    (DeRhamCoefficientComplex.coefficients p k).obj M ≃ M :=
  Equiv.ulift.trans Equiv.ulift

omit [CharP k p] in
theorem finite (M : ModuleCat.{u} k) [Module.Finite k M] :
    Module.Finite (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      ((DeRhamCoefficientComplex.coefficients p k).obj M) := by
  let : Finite M := Module.finite_of_finite k
  let : Finite ((DeRhamCoefficientComplex.coefficients p k).obj M) :=
    Finite.of_equiv M (carrierEquiv p k M).symm
  exact Module.Finite.of_finite

instance preservesLimits : PreservesLimitsOfSize.{u, u} (DeRhamCoefficientComplex.coefficients p k) where
  preservesLimitsOfShape {T} _ := by
    let : PreservesLimitsOfSize.{u, u}
        (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) :=
      preservesLimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    dsimp only [DeRhamCoefficientComplex.coefficients, EtaleZero.DeRham.Comparison.coefficientFunctor,
      Crystalline.RelativeResolution.coefficientFunctor]
    infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.DeRhamCoefficientFiniteness
