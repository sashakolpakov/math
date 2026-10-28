import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSelectionSpace

/-! Paid setup for one visited signature head. The physical key workspace,
old master words and selector outputs are cleared by the command itself. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare

open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter QueryTupleVisitor
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

def cleared : List (Fin 896) :=
  [341,342,343,344,345,346,347,348,349,350,351,353,866,841]

def reset : Cmd 40 896 := .seq (.call (clearProgram 841 0 1))
  (BankRoutines.clearCmd 841 0 1 cleared)

def resetState (a : State 40 896) : State 40 896 :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks cleared a.stacks⟩

def resetCost (a : State 40 896) : ℕ :=
  2 * (a.stacks 841).length + 3 +
    (2 * (cleared.map (fun i => ((clearStacks 841 a.stacks) i).length)).sum + 45)

theorem reset_eval (a : State 40 896) : Eval reset (resetCost a) a (resetState a) := by
  have first := BankRoutines.clear_call_eval (841 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have rest := BankRoutines.clear_eval (841 : Fin 896) (0 : Fin 40) 1 cleared (by decide)
    (readRegs a.regs 0 1 none) (clearStacks 841 a.stacks) (by simp)
  have he : BankRoutines.clearBankStacks cleared (clearStacks 841 a.stacks) =
      BankRoutines.clearBankStacks cleared a.stacks := by
    funext i
    by_cases hi : i ∈ cleared
    · simp [BankRoutines.clearBankStacks, hi]
    · have h841 : i ≠ 841 := by intro h; subst i; exact hi (by decide)
      simp [BankRoutines.clearBankStacks, clearStacks, hi, h841]
  simpa only [reset, resetCost, resetState, show cleared.length = 14 from rfl,
    show 3 * 14 + 3 = 45 by omega, he, readRegs_reset] using first.seq rest

theorem reset_frame (a : State 40 896) (i : Fin 896) (hi : i ∉ cleared) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i cleared a.stacks hi

theorem reset_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((resetState a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i ∈ cleared
  · simp [resetState, BankRoutines.clearBankStacks, hi]
  · simpa only [reset_frame a i hi] using ha i

theorem reset_cost_le (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : resetCost a ≤ 30 * B + 48 := by
  have hs : (cleared.map (fun i => ((clearStacks 841 a.stacks) i).length)).sum ≤ 14 * B := by
    apply (List.sum_le_length_nsmul _ B (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      by_cases he : i = 841
      · subst i; simp
      · simpa [clearStacks, he] using ha i)).trans_eq
    simp [cleared]
  have h841 := ha 841
  unfold resetCost
  omega

/-- Only the concrete immutable input words are premises; scratch and output
readiness are established by the paid reset. -/
theorem reset_ready (a : State 40 896) (W bits : List Bool)
    (rows : List (List (List Bool)))
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words)) :
    SignatureKeyNative.Ready (resetState a) W bits rows := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (reset_frame a 141 (by decide)).trans hW
  · exact (reset_frame a 838 (by decide)).trans hbits
  · exact BankRoutines.clearBankStacks_mem 866 cleared a.stacks (by decide)
  · exact (reset_frame a 847 (by decide)).trans hrows
  · intro i h0 h12 h14 h15
    apply BankRoutines.clearBankStacks_mem
    fin_cases i <;> first | contradiction | decide

def masters : Cmd 40 896 := .seq (overwrite 141 864)
  (.seq (overwrite 847 865) (overwrite 671 175))

noncomputable def mastersState (a : State 40 896) : State 40 896 :=
  overwriteState 671 175 (overwriteState 847 865 (overwriteState 141 864 a))

theorem masters_eval (a : State 40 896) (htmp : a.stacks 841 = []) :
    Eval masters (2 * (a.stacks 864).length + 7 * (a.stacks 141).length +
      2 * (a.stacks 865).length + 7 * (a.stacks 847).length +
      2 * (a.stacks 175).length + 7 * (a.stacks 671).length + 24) a (mastersState a) := by
  have first := overwrite_eval 141 864 (by decide) (by decide) (by decide) a htmp
  have second := overwrite_eval 847 865 (by decide) (by decide) (by decide)
    (overwriteState 141 864 a)
    (by simpa only [overwriteState_frame 141 864 (by decide) a 841 (by decide)] using htmp)
  have third := overwrite_eval 671 175 (by decide) (by decide) (by decide)
    (overwriteState 847 865 (overwriteState 141 864 a))
    (by simpa only [overwriteState_frame 847 865 (by decide) _ 841 (by decide),
      overwriteState_frame 141 864 (by decide) a 841 (by decide)] using htmp)
  have all := first.seq (second.seq third)
  simp only [overwriteState_frame 141 864 (by decide) a 865 (by decide),
    overwriteState_frame 141 864 (by decide) a 847 (by decide),
    overwriteState_frame 847 865 (by decide) _ 175 (by decide),
    overwriteState_frame 847 865 (by decide) _ 671 (by decide),
    overwriteState_frame 141 864 (by decide) a 175 (by decide),
    overwriteState_frame 141 864 (by decide) a 671 (by decide)] at all
  convert all using 1
  · rfl
  · omega
  · rfl

theorem masters_stacks (a : State 40 896) :
    (mastersState a).stacks = Function.update
      (Function.update (Function.update a.stacks 864 (a.stacks 141)) 865 (a.stacks 847))
      175 (a.stacks 671) := by
  rw [mastersState, overwriteState_stacks 671 175 (by decide),
    overwriteState_stacks 847 865 (by decide),
    overwriteState_stacks 141 864 (by decide)]
  simp

theorem masters_bound (a : State 40 896) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((mastersState a).stacks i).length ≤ B :=
  overwriteState_bound 671 175 (by decide) _ B
    (overwriteState_bound 847 865 (by decide) _ B
      (overwriteState_bound 141 864 (by decide) a B ha))

def command : Cmd 40 896 := .seq reset (.seq SignatureKeyNative.command
  (.seq masters (.call NativeHeadSelect.prepareProgram)))

def program := compiled command 838 866

noncomputable def result (a : State 40 896) (keyRegs : Fin 8 → Bool)
    (selectRegs : Fin 4 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) : State 40 896 :=
  NativeHeadSelect.result (NativeHeadSelect.resetState
    (mastersState (SignatureKeyNative.outputState (resetState a) keyRegs W bits rows))) selectRegs

/-- The complete paid preparation keeps the same boundary envelope for the
next head. Its transient bound includes all896 caller stacks and the actual
compiled halt; no successful key/scratch layout is an input premise. -/
theorem run (a : State 40 896) (W bits : List Bool)
    (rows : List (List (List Bool))) (B : ℕ)
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words))
    (hrowlen : ∀ row ∈ rows, row.length = bits.length)
    (hlen : (a.stacks 670).length = (a.stacks 858).length)
    (hkey : 16 * (W.length + bits.length + (words (rows.map words)).length) +
      AttainedSignatureProgram.cost W bits rows + 1 ≤ B)
    (hselect : 11 * (a.stacks 670).length + 6 ≤ B)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ n, n + 1 ≤ 100 * B + 200 ∧ ∃ keyRegs selectRegs,
      Eval command n a (result a keyRegs selectRegs W bits rows) ∧
      Trace program (n + 1) (a.withPC (some program.entry))
        ((result a keyRegs selectRegs W bits rows).withPC none) ∧
      (∀ i, ((result a keyRegs selectRegs W bits rows).stacks i).length ≤ B) ∧
      ∀ q z, q ≤ n + 1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 996 * B + 200 := by
  have ready := reset_ready a W bits rows hW hbits hrows
  obtain ⟨nk, hnk, kr, hk, hkt, hkb⟩ :=
    SignatureKeyNative.run (resetState a) W bits rows ready hrowlen B (reset_bound a B ha)
  let keyed := SignatureKeyNative.outputState (resetState a) kr W bits rows
  have hkbound : ∀ i, (keyed.stacks i).length ≤ B := by
    intro i
    exact (hkb nk (keyed.withPC none) le_rfl hkt i).trans (max_le hkey le_rfl)
  have hks : keyed.stacks = Function.update (resetState a).stacks 866
      (signatureValue W bits rows) :=
    SignatureKeyNative.output_stacks (resetState a) kr W bits rows ready
  have hktmp : keyed.stacks 841 = [] := by
    rw [hks, Function.update_of_ne (by decide : (841 : Fin 896) ≠ 866)]
    exact BankRoutines.clearBankStacks_mem 841 cleared a.stacks (by decide)
  have hm := masters_eval keyed hktmp
  have hmbound := masters_bound keyed B hkbound
  have hframe (i : Fin 896) (hi : i ∉ cleared) (h864 : i ≠ 864) (h865 : i ≠ 865) (h175 : i ≠ 175) :
      (mastersState keyed).stacks i = a.stacks i := by
    have h866 : i ≠ 866 := by intro h; subst i; exact hi (by decide)
    rw [masters_stacks, Function.update_of_ne h175, Function.update_of_ne h865, Function.update_of_ne h864,
      hks, Function.update_of_ne h866, reset_frame a i hi]
  have hm670 := hframe 670 (by decide) (by decide) (by decide) (by decide)
  have hm858 := hframe 858 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨ns, sr, hs, hns, hsb⟩ := HeadSelectionSpace.prepare_trace_space
    (mastersState keyed) (a.stacks 670).length B
    (by simpa only [hm670, hm858] using hlen) (by simp only [hm670, le_refl])
    hselect hmbound
  have hse : Eval (.call NativeHeadSelect.prepareProgram) ns (mastersState keyed)
      (NativeHeadSelect.result (NativeHeadSelect.resetState (mastersState keyed)) sr) :=
    Eval.call _ hs
  have whole := (reset_eval a).seq (hk.seq (hm.seq hse))
  have htime : resetCost a + (nk +
      (2 * (keyed.stacks 864).length + 7 * (keyed.stacks 141).length +
        2 * (keyed.stacks 865).length + 7 * (keyed.stacks 847).length +
        2 * (keyed.stacks 175).length + 7 * (keyed.stacks 671).length + 24 + ns)) + 1 ≤
      100 * B + 200 := by
    have hr := reset_cost_le a B ha
    have hk864 := hkbound 864
    have hk141 := hkbound 141
    have hk865 := hkbound 865
    have hk847 := hkbound 847
    have hk175 := hkbound 175
    have hk671 := hkbound 671
    omega
  refine ⟨_, htime, kr, sr, whole, compiled_halt_trace whole 838 866, ?_, ?_⟩
  · exact hsb ns _ (Nat.le_refl ns) hs
  · intro q z hq hz i
    have hi : dataBits (a.withPC (some program.entry)) ≤ 896 * B :=
      StreamResources.dataBits_le_mul _ ha
    have hb := StructuredSpace.local_stack_bound program (steps := 100 * B + 200) hi
      q z (hq.trans htime) hz i
    omega

theorem result_frame (a : State 40 896) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words))
    (i : Fin 896) (hi : i ∉ cleared) (h864 : i ≠ 864) (h865 : i ≠ 865) (h175 : i ≠ 175)
    (hselect : i ∉ NativeHeadSelect.changed) :
    (result a kr sr W bits rows).stacks i = a.stacks i := by
  have h866 : i ≠ 866 := by intro h; subst i; exact hi (by decide)
  rw [result, NativeHeadSelect.prepared_frame _ sr i hselect, masters_stacks,
    Function.update_of_ne h175, Function.update_of_ne h865, Function.update_of_ne h864,
    SignatureKeyNative.output_stacks _ kr W bits rows (reset_ready a W bits rows hW hbits hrows),
    show SignatureKeyNative.stackPorts 14 = 866 from rfl,
    Function.update_of_ne h866, reset_frame a i hi]

/-- All DFS flags and every register outside the key routine's eight-register
bank survive the complete preparation. No register-save service is assumed. -/
theorem result_register_frame (a : State 40 896) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool))) (j : Fin 40) (hj : 8 ≤ j.val) :
    (result a kr sr W bits rows).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro h; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
  have ho (src dst : Fin 896) (b : State 40 896) :
      (overwriteState src dst b).regs j = b.regs j := by
    change readRegs (readRegs b.regs 0 1 none) 0 1 none j = b.regs j
    rw [readRegs_frame _ 0 1 j none h0 h1, readRegs_frame _ 0 1 j none h0 h1]
  have hs (b : State 40 896) : (NativeHeadSelect.result b sr).regs j = b.regs j := by
    have hn : ¬ ∃ i, NativeHeadSelect.regs i = j := by
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      have hil := i.isLt
      dsimp [NativeHeadSelect.regs] at hv
      omega
    rw [NativeHeadSelect.result, embedState_register_frame _ _ _ _ j hn]
    change readRegs (readRegs b.regs 0 1 none) 0 1 none j = b.regs j
    rw [readRegs_frame _ 0 1 j none h0 h1, readRegs_frame _ 0 1 j none h0 h1]
  rw [result, hs]
  change readRegs (mastersState _).regs 0 1 none j = a.regs j
  rw [readRegs_frame _ 0 1 j none h0 h1, mastersState, ho, ho, ho,
    SignatureKeyNative.output_register_frame _ kr W bits rows j hj]
  exact readRegs_frame a.regs 0 1 j none h0 h1

/-- The masters used by the subsequent restricted head sum are produced by
the same run, while the actual ambient mask and correction word are preserved. -/
theorem result_words (a : State 40 896) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words)) :
    let out := result a kr sr W bits rows
    out.stacks 864 = W ∧ out.stacks 865 = words (rows.map words) ∧
      out.stacks 866 = signatureValue W bits rows ∧
      out.stacks 867 = OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected true
        (a.stacks 670) (a.stacks 858) ∧
      out.stacks 868 = List.replicate
        (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670)) true := by
  let keyed := SignatureKeyNative.outputState (resetState a) kr W bits rows
  have hks : keyed.stacks = Function.update (resetState a).stacks 866
      (signatureValue W bits rows) :=
    SignatureKeyNative.output_stacks _ kr W bits rows (reset_ready a W bits rows hW hbits hrows)
  have hm : (mastersState keyed).stacks = Function.update
      (Function.update (Function.update (Function.update (resetState a).stacks 866 (signatureValue W bits rows))
        864 W) 865 (words (rows.map words))) 175 (a.stacks 671) := by
    rw [masters_stacks, hks]
    simp only [Function.update_of_ne (by decide : (141 : Fin 896) ≠ 866),
      Function.update_of_ne (by decide : (847 : Fin 896) ≠ 866),
      Function.update_of_ne (by decide : (671 : Fin 896) ≠ 866),
      reset_frame a 141 (by decide), reset_frame a 847 (by decide),
      reset_frame a 671 (by decide), hW, hrows]
  have hm670 : (mastersState keyed).stacks 670 = a.stacks 670 := by
    rw [hm]
    simp only [Function.update_of_ne (by decide : (670 : Fin 896) ≠ 175),
      Function.update_of_ne (by decide : (670 : Fin 896) ≠ 865),
      Function.update_of_ne (by decide : (670 : Fin 896) ≠ 864),
      Function.update_of_ne (by decide : (670 : Fin 896) ≠ 866), reset_frame a 670 (by decide)]
  have hm858 : (mastersState keyed).stacks 858 = a.stacks 858 := by
    rw [hm]
    simp only [Function.update_of_ne (by decide : (858 : Fin 896) ≠ 175),
      Function.update_of_ne (by decide : (858 : Fin 896) ≠ 865),
      Function.update_of_ne (by decide : (858 : Fin 896) ≠ 864),
      Function.update_of_ne (by decide : (858 : Fin 896) ≠ 866), reset_frame a 858 (by decide)]
  dsimp only
  unfold result
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [NativeHeadSelect.prepared_frame _ sr 864 (by decide), hm]
    simp
  · rw [NativeHeadSelect.prepared_frame _ sr 865 (by decide), hm]
    simp
  · rw [NativeHeadSelect.prepared_frame _ sr 866 (by decide), hm]
    simp
  · rw [NativeHeadSelect.prepared_E, hm670, hm858]
  · rw [NativeHeadSelect.prepared_H, hm670]

/-- The loader's selected factor records are installed once for the complete
head rescan, in the exact physical bank consumed by the factor loop. -/
theorem result_factors (a : State 40 896) (kr : Fin 8 → Bool) (sr : Fin 4 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool)))
    (hW : a.stacks 141 = W) (hbits : a.stacks 838 = bits)
    (hrows : a.stacks 847 = words (rows.map words)) :
    (result a kr sr W bits rows).stacks 175 = a.stacks 671 := by
  rw [result, NativeHeadSelect.prepared_frame _ sr 175 (by decide), masters_stacks,
    Function.update_self, SignatureKeyNative.output_stacks _ kr W bits rows
      (reset_ready a W bits rows hW hbits hrows),
    show SignatureKeyNative.stackPorts 14 = 866 from rfl,
    Function.update_of_ne (by decide : (671 : Fin 896) ≠ 866), reset_frame a 671 (by decide)]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare
