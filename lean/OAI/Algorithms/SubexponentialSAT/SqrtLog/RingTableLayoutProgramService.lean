import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgramBridge

namespace OAI.Algorithms

/-!
Integration ABI: two Boolean registers and eighteen stacks. Inputs are the
power-major bit stream on stack 0, a list of length d on stack 1, and a list
of length B on stack 2. Stack 3 receives the forward table. Stacks 4 through
17 are empty on entry and exit. The three inputs are preserved; the registers
are scratch. Neither d nor B occurs in the command's finite control.

Offsets are maintained as unary lists. Each scalar at (i+j)*d+k is fetched by
the native preserving array reader; its bits are transferred to a reverse
accumulator. A final native transfer restores the required forward order.
-/

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpQuarticRing

/-- Embeddable command contract for the power-generation/table-layout service. -/
theorem power_table_command_eval {d B : ℕ} (P : ℕ → Fin d → Word B)
    (degree width : List Bool) (regs : Fin 2 → Bool)
    (hd : degree.length = d) (hw : width.length = B) :
    ∃ n ≤ budget d B, ∃ rf,
      Eval command n (state regs (initial (powerRecords P (2*d-1)).flatten degree width))
        (state rf {(initial (powerRecords P (2*d-1)).flatten degree width) with
          out := RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k)}) := by
  have h := command_eval (powerRecords P (2*d-1)) degree width regs
    (by simpa only [hw] using powerRecords_width P (2*d-1))
    (by simp [hd, Nat.mul_comm])
  simpa only [hd, hw, power_layout_eq_tableEncoding] using h

theorem power_table_output_length {d B : ℕ} (P : ℕ → Fin d → Word B) :
    (RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k)).length = d^3*B := by
  rw [← power_layout_eq_tableEncoding]
  exact full_layout_length _ d B (powerRecords_width P (2*d-1)) (by simp [Nat.mul_comm])

theorem power_input_length {d B : ℕ} (P : ℕ → Fin d → Word B) :
    (powerRecords P (2*d-1)).flatten.length = (2*d-1)*d*B := by
  have h := ArrayUpdatePrograms.uniform_flatten_length (powerRecords P (2*d-1)) B
    (powerRecords_width P (2*d-1))
  simpa using h

/-- A dimension-independent finite program with a polynomial native trace bound. -/
theorem power_table_native_polynomial {d B : ℕ} (P : ℕ → Fin d → Word B)
    (degree width : List Bool) (regs : Fin 2 → Bool)
    (hd : degree.length = d) (hw : width.length = B) :
    ∃ rf, RunsIn program (1000*(d+1)^5*(B+1))
      ((state regs (initial (powerRecords P (2*d-1)).flatten degree width)).withPC
        (some program.entry))
      ((state rf {(initial (powerRecords P (2*d-1)).flatten degree width) with
        out := RingTriple.tableEncoding (fun i j k => P (i.val+j.val) k)}).withPC none) := by
  obtain ⟨rf, n, hn, ht⟩ := power_table_program_run P degree width regs hd hw
  exact ⟨rf, n, hn.trans (budget_polynomial d B), ht⟩

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
