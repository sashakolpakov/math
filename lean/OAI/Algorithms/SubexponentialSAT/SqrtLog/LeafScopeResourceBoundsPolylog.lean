import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBoundsStatistics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyCodeParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectTermination

namespace OAI.Algorithms

/-! Explicit, pointwise polylogarithmic resource envelopes. No sequence of
matrices is chosen before the ambient cutoff: all raw scope tables satisfying
the concrete slot budget share these same constants. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open Asymptotic LeafStatisticsProgram

abbrev slotCoefficient (q : ℕ) := 320000*(q+2)^3 + 20000*(q+2)^2 + 1
abbrev massCoefficient (k q : ℕ) := 11 * slotCoefficient q * (k+1)
abbrev statCoefficient (k q : ℕ) := 2 * massCoefficient k q + 1
abbrev resourceExponent (q : ℕ) := 2*q+4

theorem code_bounds (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    SparseCode.degreeBound m B ≤ slotCoefficient q * L n^(2*q+3) ∧
    SparseCode.distanceDenom m B ≤ slotCoefficient q * L n^(2*q+3) := by
  constructor
  · exact (CostAssembly.code_degreeBound_le n m B q hm hB).trans
      (Nat.mul_le_mul_right _ (by dsimp [slotCoefficient]; omega))
  · apply (CostAssembly.code_distanceDenom_le n m B q hm hB).trans
    apply Nat.mul_le_mul
    · dsimp [slotCoefficient]; omega
    · exact Nat.pow_le_pow_right (L_pos n) (by omega)

theorem raw_mass_polylog (n m B k q : ℕ) (hn : 0 < n) (hm : m ≤ n*B)
    (hB : B ≤ L n^q) (hsize : Nat.size m ≤ n) (S : ℕ)
    (hS : S ≤ (3*n*SparseCode.degreeBound m B +
      (HashSelect.loopCap n m+1)*SparseCode.distanceDenom m B+1)*k) :
    S ≤ n * (massCoefficient k q * L n^(2*q+3)) := by
  obtain ⟨hD,hP⟩ := code_bounds n m B q hm hB
  have hK : HashSelect.loopCap n m+1 ≤ 7*n := by
    dsimp [HashSelect.loopCap]; omega
  have hU : 1 ≤ slotCoefficient q * L n^(2*q+3) := by
    have hpow := Nat.one_le_pow (2*q+3) (L n) (L_pos n)
    have hc : 1 ≤ slotCoefficient q := by dsimp [slotCoefficient]; omega
    nlinarith
  calc
    S ≤ (3*n*SparseCode.degreeBound m B +
      (HashSelect.loopCap n m+1)*SparseCode.distanceDenom m B+1)*k := hS
    _ ≤ (3*n*(slotCoefficient q*L n^(2*q+3)) +
      (7*n)*(slotCoefficient q*L n^(2*q+3))+n*(slotCoefficient q*L n^(2*q+3)))*k := by
        apply Nat.mul_le_mul_right
        apply Nat.add_le_add
        · exact Nat.add_le_add (Nat.mul_le_mul_left _ hD) (Nat.mul_le_mul hK hP)
        · nlinarith
    _ ≤ n * (massCoefficient k q * L n^(2*q+3)) := by
      dsimp [massCoefficient]
      nlinarith only [Nat.zero_le (n*(slotCoefficient q*L n^(2*q+3)))]

theorem raw_arity_polylog (n m B k q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q)
    (A : ℕ) (hA : A ≤ (SparseCode.degreeBound m B + SparseCode.distanceDenom m B+1)*k) :
    A ≤ massCoefficient k q * L n^(2*q+3) := by
  obtain ⟨hD,hP⟩ := code_bounds n m B q hm hB
  have hpow := Nat.one_le_pow (2*q+3) (L n) (L_pos n)
  have hc : 1 ≤ slotCoefficient q := by dsimp [slotCoefficient]; omega
  have hU : 1 ≤ slotCoefficient q * L n^(2*q+3) := by nlinarith
  calc
    A ≤ (SparseCode.degreeBound m B + SparseCode.distanceDenom m B+1)*k := hA
    _ ≤ (3*(slotCoefficient q*L n^(2*q+3)))*k := by
      apply Nat.mul_le_mul_right
      omega
    _ ≤ massCoefficient k q * L n^(2*q+3) := by
      dsimp [massCoefficient]
      nlinarith only [Nat.zero_le (slotCoefficient q*L n^(2*q+3)),
        Nat.zero_le (k*(slotCoefficient q*L n^(2*q+3)))]

/-- Both native statistics have a common fixed envelope, including the neutral
singleton factors. `nb` and `tb` are the actual binary Prepare inputs. -/
theorem measured_polylog (n m B k q : ℕ) (hn : 0 < n) (hm : m ≤ n*B)
    (hB : B ≤ L n^q) (hsize : Nat.size m ≤ n)
    (scopes : List (List ℕ)) (nb tb : List Bool)
    (hnb : BinaryArithmetic.toNat nb = n)
    (htb : BinaryArithmetic.toNat tb = Nat.sqrt (L n)+1)
    (hS : HighIncidenceProgram.Prepare.mass scopes ≤
      (3*n*SparseCode.degreeBound m B+(HashSelect.loopCap n m+1)*SparseCode.distanceDenom m B+1)*k)
    (hA : ∀ row ∈ scopes, row.length ≤ (SparseCode.degreeBound m B+SparseCode.distanceDenom m B+1)*k) :
    let mask := forwardMask scopes (HighIncidenceProgram.Prepare.cut scopes nb tb) n
    (measured scopes mask).occurrence ≤ statCoefficient k q * L n^resourceExponent q ∧
    max (Arity.arity mask scopes 0) (if (measured scopes mask).uncovered=0 then 0 else 1) ≤
      statCoefficient k q * L n^resourceExponent q := by
  have hs := raw_mass_polylog n m B k q hn hm hB hsize _ hS
  have ha := fun row hr => raw_arity_polylog n m B k q hm hB row.length (hA row hr)
  have hp : 1 ≤ L n^(2*q+3) := Nat.one_le_pow _ _ (L_pos n)
  have hl : 1 ≤ L n := L_pos n
  have hc : 1 ≤ massCoefficient k q := by
    change 0 < massCoefficient k q
    dsimp [massCoefficient, slotCoefficient]
    positivity
  have ht : Nat.sqrt (L n)+1 ≤ 2*L n := by have := Nat.sqrt_le_self (L n); omega
  have hpow : L n^resourceExponent q = L n^(2*q+3) * L n := by
    unfold resourceExponent
    convert pow_succ (L n) (2*q+3) using 1
  have hone : 1 ≤ statCoefficient k q * L n^resourceExponent q := by
    rw [hpow]
    change 0 < statCoefficient k q * (L n^(2*q+3)*L n)
    dsimp [statCoefficient]
    positivity
  have hout : (massCoefficient k q * L n^(2*q+3)) * (Nat.sqrt (L n)+1) ≤
      statCoefficient k q * L n^resourceExponent q := by
    rw [hpow]
    calc
      _ ≤ (massCoefficient k q * L n^(2*q+3)) * (2*L n) := Nat.mul_le_mul_left _ ht
      _ ≤ _ := by dsimp [statCoefficient]; nlinarith only [Nat.zero_le (L n^(2*q+3)*L n)]
  have hsmall : massCoefficient k q * L n^(2*q+3) ≤ statCoefficient k q * L n^resourceExponent q := by
    rw [hpow]
    calc
      _ ≤ (massCoefficient k q * L n^(2*q+3))*L n := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (massCoefficient k q * L n^(2*q+3)) hl
      _ = massCoefficient k q * (L n^(2*q+3)*L n) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by dsimp [statCoefficient]; omega)
  constructor
  · have hh := measured_occurrence_of_mass scopes nb tb
      (massCoefficient k q * L n^(2*q+3)) (by simpa [hnb] using hn) (by simpa [hnb] using hs)
    rw [hnb,htb] at hh
    exact hh.trans (max_le hone hout)
  · exact (measured_arity_le scopes _ _ ha).trans (max_le hsmall hone)

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
