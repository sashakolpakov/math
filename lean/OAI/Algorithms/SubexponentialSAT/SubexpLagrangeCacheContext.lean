import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheWorkspace
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheControl
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCachePreparation

namespace OAI.Algorithms

/-! Exact correspondence between the physical eight-master preparation and
the typed arithmetic workspace used by the cache loops. -/

namespace SubexponentialSAT.SubexpLagrangeCacheContext

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheWorkspace
open SubexpLagrangeCachePreparation

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

abbrev Coefficient := Quad (SubexpQuarticRing.Word (baseWidth p μ))

structure Valid (x : Inputs) (t zero one : Coefficient p μ)
    (minusOne : SubexpQuarticRing.Word (baseWidth p μ)) : Prop where
  prime : primeValue x = p
  modulus : x.modulus = M.bits
  width : x.width.length = baseWidth p μ
  reduction : x.reduction = SubexpQuarticFlatMul.flat t
  unit : x.unit = SubexpFlatAdd.encode one
  minus : x.minusOne = minusOne.val
  zero : SubexpFlatAdd.encode zero = List.replicate (4 * baseWidth p μ) false
  precision : CounterPrograms.value x.precision = μ
  exponent : BinaryArithmetic.toNat x.exponent = p ^ 4 - 2

omit [Fact p.Prime] in
theorem prepared_workspace (x : Inputs) (t zero one : Coefficient p μ)
    (minusOne : SubexpQuarticRing.Word (baseWidth p μ))
    (H : Valid p μ M x t zero one minusOne) :
    Ready M.bits x.width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) (preparedStore x) := by
  intro i hi
  have hn (j : Fin 256) (hj : 205 ≤ j.val) : i ≠ j := by
    intro he
    subst i
    omega
  have hraw : rawStore x i = [] := by
    simp [rawStore, hn 206 (by decide), hn 207 (by decide), hn 208 (by decide),
      hn 209 (by decide), hn 210 (by decide), hn 211 (by decide),
      hn 224 (by decide), hn 225 (by decide)]
  simp only [preparedStore, allocatedStore, cellStore,
    Function.update_of_ne (hn 246 (by decide)),
    Function.update_of_ne (hn 250 (by decide)),
    Function.update_of_ne (hn 217 (by decide)),
    Function.update_of_ne (hn 213 (by decide)),
    Function.update_of_ne (hn 242 (by decide)),
    Function.update_of_ne (hn 243 (by decide))]
  by_cases h104 : i = 104
  · subst i
    simp [parameterStore, layout, zeroCell, H.width]
  · by_cases h201 : i = 201
    · subst i
      simp [parameterStore, layout, H.reduction]
    · by_cases h202 : i = 202
      · subst i
        simp [parameterStore, layout]
      · by_cases h10 : i = 10
        · subst i
          simp [parameterStore, layout]
        · by_cases h194 : i = 194
          · subst i
            simp [parameterStore, layout, H.modulus]
          · by_cases h5 : i = 5
            · subst i
              simp [parameterStore, layout, H.modulus]
            · simp [parameterStore, layout, h104, h201, h202, h10, h194, h5, hraw]

def support : List (Fin 256) :=
  [5, 10, 104, 194, 201, 202, 206, 207, 208, 209, 210, 211, 213, 217, 224, 225,
    242, 243, 246, 250]

theorem prepared_empty (x : Inputs) (i : Fin 256) (hi : i ∉ support) :
    preparedStore x i = [] := by
  simp only [support, List.mem_cons, not_or] at hi
  rcases hi with ⟨h5, h10, h104, h194, h201, h202, h206, h207, h208, h209,
    h210, h211, h213, h217, h224, h225, h242, h243, h246, h250⟩
  simp [preparedStore, allocatedStore, cellStore, parameterStore, rawStore,
    h5, h10, h104, h194, h201, h202, h206, h207, h208, h209, h210, h211,
    h213, h217, h224, h225, h242, h243, h246, h250]

omit [Fact p.Prime] in
theorem prepared_high (x : Inputs) (t zero one : Coefficient p μ)
    (minusOne : SubexpQuarticRing.Word (baseWidth p μ))
    (H : Valid p μ M x t zero one minusOne) :
    preparedStore x 207 = SubexpFlatAdd.encode one ∧
    preparedStore x 211 = minusOne.val ∧
    preparedStore x 213 = SubexpFlatAdd.encode zero ∧
    preparedStore x 217 = SubexpFlatAdd.encode zero ∧
    preparedStore x 224 = x.precision ∧ preparedStore x 225 = x.exponent ∧
    preparedStore x 243 = List.replicate p true ∧
    preparedStore x 246 = List.replicate p true ∧
    preparedStore x 250 = Subexp.FactorPacketCoordinates.cacheBytes [] := by
  simp [preparedStore, allocatedStore, cellStore, parameterStore, rawStore,
    zeroCell, unaryPrime, H.unit, H.minus, H.zero, H.prime, H.width,
    Subexp.FactorPacketCoordinates.cacheBytes, ProgramEncoding.encodeRecords,
    Encoding.encodeList]

omit [Fact p.Prime] in
theorem prepared_zeroArray (x : Inputs) (t zero one : Coefficient p μ)
    (minusOne : SubexpQuarticRing.Word (baseWidth p μ))
    (H : Valid p μ M x t zero one minusOne) :
    preparedStore x 242 = SubexpConvolutionEncoding.encodeArray SubexpFlatAdd.encode
      (List.replicate p zero) := by
  simp only [preparedStore, allocatedStore, Function.update_of_ne (show (242 : Fin 256) ≠ 246 by decide),
    Function.update_of_ne (show (242 : Fin 256) ≠ 250 by decide),
    Function.update_of_ne (show (242 : Fin 256) ≠ 217 by decide),
    Function.update_of_ne (show (242 : Fin 256) ≠ 213 by decide), Function.update_self]
  rw [zeroArray_eq, H.prime, H.width]
  simp only [SubexpConvolutionEncoding.encodeArray, List.map_replicate, H.zero,
    SubexpLinearFactorEncoding.flatten_replicate_false]

end SubexponentialSAT.SubexpLagrangeCacheContext

end OAI.Algorithms
