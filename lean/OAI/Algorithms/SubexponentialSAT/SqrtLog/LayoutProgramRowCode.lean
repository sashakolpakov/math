import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumeratorBridge
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithmEntry
import OAI.Algorithms.SubexponentialSAT.SubexpRepresentedRows

namespace OAI.Algorithms

/-! The literal represented source-row circuit over the target ring. Integer
numerators are lifted directly, then multiplied by the supplied inverse of the
power-of-two denominator. There is no field section or inverse in the target
ring. The bit-program realizations of these measured scalar operations and
of the cache construction are separate obligations. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpRowInterpolation
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpTaylorExecution
open LayoutScaledMatrices

variable {C O : Type*} {r Q Δ : ℕ}

def sourceValue (ops : RingProgram C) (integerWord : ℤ → C) (inverseDenominator : C)
    (A R : ℕ) (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) (t : Fin Q) : C :=
  if u ∈ joint t (y.head t) i ∧ y ∈ joint t (y.head t) i then
    (ops.negRun (ops.mulRun inverseDenominator
      (integerWord (LayoutCoefficientAlgorithm.scalarEntry i t A R u y))).1).1
  else ops.zeroRun.1

def sourceCode (ops : RingProgram C) (cache : NodeCache C Q)
    (integerWord : ℤ → C) (inverseDenominator : C)
    (A R : ℕ) (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) : PolynomialCode C :=
  row ops cache u (fun y => y.head) (u.slot i) R
    (sourceValue ops integerWord inverseDenominator A R u i) y

variable [CommRing O] (ops : RepresentedRing C O)
variable (integerWord : ℤ → C) (hinteger : ∀ z, ops.decode (integerWord z) = (z : O))
variable (denominator : Oˣ) (inverseDenominator : C)
variable (hinverse : ops.decode inverseDenominator = (↑(denominator⁻¹) : O))

include hinteger hinverse in
theorem sourceValue_decode (A R : ℕ) (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) (t : Fin Q) :
    ops.decode (sourceValue ops.program integerWord inverseDenominator A R u i y t) =
      SubexponentialSAT.SubexpAnnihilation.matrixPrescription (RingHom.id O)
        (fun t g j => unitScaled denominator (LayoutNumerator.family r Q Δ A R t g j))
        u i y t := by
  by_cases hu : u ∈ joint t (y.head t) i <;>
    by_cases hy : y ∈ joint t (y.head t) i
  all_goals
    simp [sourceValue, hu, hy, ops.zero_correct,
      ops.neg_correct, ops.mul_correct, hinteger, hinverse,
      SubexponentialSAT.SubexpAnnihilation.matrixPrescription,
      SubexponentialSAT.SubexpAnnihilation.zeroExtendMatrix, unitScaled,
      LayoutNumerator.family, LayoutNumerator.joint,
      LayoutCoefficientAlgorithm.scalarEntry_eq_entry]

include hinteger hinverse in
theorem sourceCode_decode (cache : NodeCache C Q) {node : Fin Q → O}
    (units : NodeUnits node)
    (hnode : ∀ t, ops.decode (cache.node t) = node t)
    (hnodeInv : ∀ t, ops.decode (cache.inverse t) = units.nodeInverse t)
    (hdiff : ∀ t s, ops.decode (cache.difference t s) = units.differenceInverse t s)
    (A R : ℕ) (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) :
    (mapCode ops.decode (sourceCode ops.program cache integerWord inverseDenominator A R u i y)).denote =
      sourceRow (LayoutNumerator.family r Q Δ A R) denominator u i R units y := by
  unfold sourceCode
  rw [map_row ops cache units hnode hnodeInv hdiff, mismatchRowCode_denote]
  unfold sourceRow SubexponentialSAT.SubexpAnnihilation.rowForMatrices
  congr 2
  funext y t
  exact sourceValue_decode ops integerWord hinteger denominator inverseDenominator hinverse A R u i y t

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
