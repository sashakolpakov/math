import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCost

/-! Actual sparse-row serialization and its same-run source resource bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

/-- Every retained source input of the actual sparse-row serializer. In the
scheduled construction its vertex count is polynomial by graph_edge_upper. -/
def rowsInputSpan (r D t : ℕ) (dword mword width : List Bool) : ℕ :=
  dword.length + mword.length + width.length + D + t + 2 ^ r +
    5 * (D * r) + 5 * (t * D) + r

theorem rows_input_bound {r D t : ℕ} (regs : Fin 16 → Bool)
    (dword mword width : List Bool) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (i : Fin 64) :
    ((CodeRowsProgram.inputState regs dword mword width shifts Q).stacks i).length ≤
      rowsInputSpan r D t dword mword width := by
  have hvertices : 0 < 2 ^ r := Nat.two_pow_pos r
  simp only [CodeRowsProgram.inputState]
  split_ifs <;> simp only [rowsInputSpan, List.length_replicate, List.length_nil,
    CodeSearchProgram.matrixFrames_binary_length, CodeSearchProgram.matrixFrames_ternary_length]
  all_goals omega

/-- The serializer emits the actual incidence-slot words for the supplied
candidates. Its same trace has a local time bound and all-stack prefix bound. -/
theorem rows_runs_space {r D t m : ℕ} (regs : Fin 16 → Bool)
    (dword mword width : List Bool) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (hd : BinaryArithmetic.toNat dword = D) (hm : BinaryArithmetic.toNat mword = m)
    (hcap : 3 * m ≤ 2 ^ width.length) :
    ∃ steps rf, steps ≤ CodeRowsProgram.explicitCost r D t width.length dword.length mword.length ∧
      Trace CodeRowsProgram.program steps
        ((CodeRowsProgram.inputState regs dword mword width shifts Q).withPC
          (some CodeRowsProgram.program.entry))
        ((CodeRowsProgram.outputState (m := m) rf dword mword width shifts Q).withPC none) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace CodeRowsProgram.program prefixSteps
          ((CodeRowsProgram.inputState regs dword mword width shifts Q).withPC
            (some CodeRowsProgram.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ rowsInputSpan r D t dword mword width +
          CodeRowsProgram.explicitCost r D t width.length dword.length mword.length) := by
  obtain ⟨rf, steps, hn, he⟩ := CodeRowsProgram.program_runsIn_explicit
    regs dword mword width shifts Q hd hm hcap
  refine ⟨steps, rf, hn, he, ?_⟩
  intro prefixSteps intermediate hle hp i
  have hg := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le hp i
  have hi := rows_input_bound regs dword mword width shifts Q i
  change (intermediate.stacks i).length ≤
    ((CodeRowsProgram.inputState regs dword mword width shifts Q).stacks i).length + prefixSteps at hg
  omega

/-- The runtime vertex word supplied to the serializer is polynomial in m;
its length is not the number of searched graph candidates. -/
theorem selected_vertex_count_le {m B : ℕ} (hm : 0 < m) (hB : 0 < B) :
    2 ^ SparseCode.dimension m B ≤ 2 * m := by
  have hpos := SparseCode.degree_pos hm hB
  have hbound := SparseCode.graph_edge_upper hm hB
  have hmul := Nat.mul_le_mul_left (2 ^ SparseCode.dimension m B) hpos
  simpa only [Nat.mul_one] using hmul.trans hbound.le

/-- Physical serialized rows inherit the selected graph/local-code guarantee.
Coverage, rather than agreement with an earlier search order, is sufficient. -/
theorem emitted_rows_kernel_bound {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B)
    (hs : WalshExistence.Good (SparseCode.gapDenom m B) shifts)
    (hQ : SparseCode.HasDistance Q
      (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1))
    (w : Fin m → SparseCode.F3)
    (hw : ∀ row ∈ CodeRowsProgram.serializedRows m shifts Q,
      (∑ c, CodeRowsProgram.coefficient row c * w c) = 0) (hw0 : w ≠ 0) :
    m ≤ SparseCode.distanceDenom m B * SparseCode.weight w :=
  CodeRowsProgram.serializedRows_kernel_bound hm hB shifts Q hs hQ w hw hw0

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- The serializer's whole retained input span is polynomial once the actual
vertex count bound and runtime word-length bounds have been established. -/
theorem rowsInputSpan_le {r D t S : ℕ} (dword mword width : List Bool)
    (hS : 1 ≤ S) (hr : r ≤ S) (hD : D ≤ S) (ht : t ≤ S)
    (hd : dword.length ≤ S) (hm : mword.length ≤ S) (hw : width.length ≤ S)
    (hvertices : 2 ^ r ≤ 2 * S) :
    rowsInputSpan r D t dword mword width ≤ 20 * S ^ 2 := by
  have hDr : D * r ≤ S * S := Nat.mul_le_mul hD hr
  have htD : t * D ≤ S * S := Nat.mul_le_mul ht hD
  unfold rowsInputSpan
  nlinarith

/-- Actual complete code-row production, after the graph-order inequality
has bounded its only exponential domain by the clause count. -/
theorem codeRows_explicitCost_le (r D t b Ld Lm S : ℕ) (hS : 1 ≤ S)
    (hr : r ≤ S) (hD : D ≤ S) (ht : t ≤ S) (hb : b ≤ S)
    (hdword : Ld ≤ S) (hmword : Lm ≤ S) (hvertices : 2 ^ r ≤ 2 * S) :
    SqrtLog.CodeRowsProgram.explicitCost r D t b Ld Lm ≤ 1000000 * S ^ 5 := by
  have hrow : SqrtLog.CodeRowsProgram.explicitRowCost r D b Ld Lm ≤ 200000 * S ^ 3 := by
    have h1 : S ≤ S ^ 3 := Nat.le_self_pow (by decide) _
    have h2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
    have h0 : 1 ≤ S ^ 3 := one_le_pow₀ hS
    calc
      _ ≤ 7 * S + 35 * (S * S) + S * (2000 * (5 * S + 4) ^ 2 + 2) +
          2 * S + 4 * (S * S) + 23 := by
        unfold SqrtLog.CodeRowsProgram.explicitRowCost
        gcongr
        omega
      _ ≤ _ := by nlinarith
  have h1 : S ≤ S ^ 5 := Nat.le_self_pow (by decide) _
  have h2 : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S ^ 3 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  have h0 : 1 ≤ S ^ 5 := one_le_pow₀ hS
  calc
    _ ≤ 2 * S * (2 * (35 * (S * S) + 7 * S + S * (200000 * S ^ 3 + 2) + 13) +
        8 * S + 10) + 13 * S + 18 := by
      unfold SqrtLog.CodeRowsProgram.explicitCost
      gcongr
    _ ≤ _ := by nlinarith

/-- One actual serializer trace has both polynomial running time and a
polynomial bound on every stack at every prefix, including its compiled halt. -/
theorem rows_runs_polynomial {r D t m S : ℕ} (regs : Fin 16 → Bool)
    (dword mword width : List Bool) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3)
    (hd : BinaryArithmetic.toNat dword = D) (hm : BinaryArithmetic.toNat mword = m)
    (hcap : 3 * m ≤ 2 ^ width.length) (hS : 1 ≤ S)
    (hr : r ≤ S) (hD : D ≤ S) (ht : t ≤ S)
    (hdword : dword.length ≤ S) (hmword : mword.length ≤ S)
    (hwidth : width.length ≤ S) (hvertices : 2 ^ r ≤ 2 * S) :
    ∃ steps rf, steps ≤ 1000000 * S ^ 5 ∧
      Trace CodeRowsProgram.program steps
        ((CodeRowsProgram.inputState regs dword mword width shifts Q).withPC
          (some CodeRowsProgram.program.entry))
        ((CodeRowsProgram.outputState (m := m) rf dword mword width shifts Q).withPC none) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace CodeRowsProgram.program prefixSteps
          ((CodeRowsProgram.inputState regs dword mword width shifts Q).withPC
            (some CodeRowsProgram.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 1000020 * S ^ 5) := by
  obtain ⟨steps, rf, hn, he, hp⟩ := rows_runs_space regs dword mword width shifts Q hd hm hcap
  have hc := codeRows_explicitCost_le r D t width.length dword.length mword.length S
    hS hr hD ht hwidth hdword hmword hvertices
  have hi := rowsInputSpan_le dword mword width hS hr hD ht hdword hmword hwidth hvertices
  have hpow : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by decide)
  refine ⟨steps, rf, hn.trans hc, he, ?_⟩
  intro prefixSteps intermediate hle ht i
  have hs := hp prefixSteps intermediate hle ht i
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeProgram
