import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCallback
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCandidateBounds
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerInputBounds

namespace OAI.Algorithms

/-!
# Uniform bit-size envelope for the actual masked-candidate callback

The aggregate includes the actual encoded formula and control-word lengths.
No decoded integer is used as a substitute for a bit-word length.
-/

namespace SubexponentialSAT.ExecSunflowerCallbackBounds

open CandidatePrepareProgram

/-- One fixed polynomial bounds every actual callback for the supplied tuple
shape, including preparation, checking, witness handling, and cleanup. -/
theorem bound_le_aggregate (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (k r w : ℕ)
    (hm : mask.length = k) (hw : words.map List.length = List.replicate r w) :
    ExecSunflowerCallback.bound F mask limit width size words ≤
      3000000 * (aggregate F k r w limit width size) ^ 8 := by
  let N := aggregate F k r w limit width size
  let A := (formulaCode F).length
  let T := (tupleCode (mask :: words)).length
  let G := selected F words
  let H := core F mask words
  have hN : 1 ≤ N := by dsimp [N, aggregate]; omega
  have hA : A + 1 ≤ N := by dsimp [N, A, aggregate]; omega
  have hk : k ≤ N := by dsimp [N, aggregate]; omega
  have hr : r ≤ N := by dsimp [N, aggregate]; omega
  have hwN : w ≤ N := by dsimp [N, aggregate]; omega
  have hwidth : width.length ≤ N := by dsimp [N, aggregate]; omega
  have hsize : size.length ≤ N := by dsimp [N, aggregate]; omega
  have hbase : A + limit.length + 1 ≤ N := by dsimp [N, A, aggregate]; omega
  have hN2 : N ≤ N ^ 2 := by
    simpa only [pow_two, mul_one] using Nat.mul_le_mul_left N hN
  have h12 : 1 ≤ N ^ 2 := hN.trans hN2
  have hrw : r * w ≤ N ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hr hwN
  have hT : T ≤ 9 * N ^ 2 := by
    have ht := maskedTuple_length mask words k r w hm hw
    change T = _ at ht
    have hk2 := hk.trans hN2
    have hr2 := hr.trans hN2
    omega
  have hinput : CandidatePrepareProgram.inputBits F mask limit words + 1 ≤ 10 * N ^ 2 := by
    change A + T + limit.length + 1 ≤ _
    omega
  have hp : CandidatePrepareProgram.bound F mask limit words ≤ 60000 * N ^ 4 := by
    calc
      _ ≤ 600 * (CandidatePrepareProgram.inputBits F mask limit words + 1) ^ 2 :=
        CandidatePrepareProgram.bound_le_square F mask limit words
      _ ≤ 600 * (10 * N ^ 2) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hinput 2)
      _ = 60000 * N ^ 4 := by ring
  have hl : words.length = r := by simpa using congrArg List.length hw
  have hG : (formulaCode G).length ≤ 3 * N ^ 2 := by
    have hg := selected_bits_le F words
    change (formulaCode G).length ≤ 1 + (2 * A + 2) * words.length at hg
    rw [hl] at hg
    have hm' := Nat.mul_le_mul (by omega : 2 * A + 2 ≤ 2 * N) hr
    nlinarith
  have hH : (clauseCode H).length ≤ N := (core_bits_le F mask words).trans (by
    change A ≤ N
    omega)
  have hHB : (clauseCode H).length ≤ 3 * N ^ 2 := by omega
  have hwB : width.length ≤ 3 * N ^ 2 := by omega
  have hsB : size.length ≤ 3 * N ^ 2 := by omega
  have hb1 : 3 * N ^ 2 + 1 ≤ 4 * N ^ 2 := by omega
  have hc : ExecSunflowerCandidateProgram.bound G H width size ≤ 2097152 * N ^ 8 := by
    calc
      _ ≤ 8192 * (3 * N ^ 2 + 1) ^ 4 :=
        ExecSunflowerCandidateProgram.bound_le_uniform G H width size (3 * N ^ 2) hG hHB hwB hsB
      _ ≤ 8192 * (4 * N ^ 2) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb1 4)
      _ = 2097152 * N ^ 8 := by ring
  have h28 : N ^ 2 ≤ N ^ 8 := Nat.pow_le_pow_right hN (by decide)
  have h48 : N ^ 4 ≤ N ^ 8 := Nat.pow_le_pow_right hN (by decide)
  have h18 : 1 ≤ N ^ 8 := h12.trans h28
  change CandidatePrepareProgram.bound F mask limit words +
    (ExecSunflowerCandidateProgram.bound G H width size + 7 * T +
      2 * (formulaCode G).length + 2 * (clauseCode H).length + 21) + 3 ≤ 3000000 * N ^ 8
  omega

/-- The uniform polynomial bounds an execution of the actual callback
command, including the branch that retains an earlier accepted witness. -/
theorem command_eval_le_aggregate (F : Formula) (mask limit width size : List Bool)
    (words : List (List Bool)) (k r w : ℕ)
    (hm : mask.length = k) (hw : words.map List.length = List.replicate r w)
    (d : ExecSunflowerCallback.Data)
    (h : d.stacks 21 = [] → ExecSunflowerCallback.Fresh F mask limit width size words d) :
    ∃ n ≤ 3000000 * (aggregate F k r w limit width size) ^ 8,
      ∃ e : ExecSunflowerCallback.Data,
        StructuredCalls.Eval ExecSunflowerCallback.command n d e ∧
          e.stacks = ExecSunflowerCallback.outputStacks F mask limit width size words d := by
  obtain ⟨n, hn, e, he, hs⟩ :=
    ExecSunflowerCallback.command_eval F mask limit width size words d h
  exact ⟨n, hn.trans (bound_le_aggregate F mask limit width size words k r w hm hw), e, he, hs⟩

end SubexponentialSAT.ExecSunflowerCallbackBounds

end OAI.Algorithms
