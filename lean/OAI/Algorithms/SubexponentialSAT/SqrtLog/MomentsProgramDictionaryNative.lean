import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryState

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

private theorem embed_native (regs rr : Fin 8 → Bool) (a : Tape)
    (out left right steps : List Bool) :
    embedState id nativeStacks (machine regs a)
      (RingScan.addState rr a.modulus out [] left right [] steps a.width) =
    machine rr { a with out := out, left := left, right := right, steps := steps } := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id nativeStacks_injective
  · intros; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [machine,tapes,nativeStacks,Fin.exists_fin_succ]

theorem add_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (a : Tape)
    (hm : a.modulus = M.bits) (hl : a.left = RingScan.leftBits pairs)
    (hr : a.right = RingScan.rightBits pairs) (ho : a.out = [])
    (hc : a.steps.length = pairs.length) (hw : a.width.length = baseWidth p t) :
    ∃ n ≤ pairs.length * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 6,
    ∃ rr, Eval add n (machine regs a)
      (machine rr { a with out := RingScan.sumBits p t M pairs, left := [], right := [], steps := [] }) := by
  obtain ⟨rr,n,hn,ht⟩ := RingScan.addVectorProgram_run p t M pairs regs a.steps a.width hc hw
  have hh := eval_call_lifted RingScan.addVectorProgram id nativeStacks
    (machine regs a) Function.injective_id nativeStacks_injective ht
  rw [←hm,←hl,←hr] at hh
  rw [embed_native,embed_native] at hh
  have ha : { a with out := [], left := a.left, right := a.right, steps := a.steps } = a := by
    cases a; simp_all
  rw [ha] at hh
  exact ⟨n,hn,rr,hh⟩

theorem parseStacks_injective : Function.Injective parseStacks := by decide

private theorem embed_parser (regs : Fin 8 → Bool) (rr : Fin 5 → Bool)
    (a : Tape) (found left : List Bool) :
    embedState parseRegisters parseStacks (machine regs a)
      (SubexponentialSAT.SubexpRecordScan.recordState rr found left [] [] [] []) =
    machine (overlay regs rr) { a with found := found, left := left } := by
  apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective parseStacks_injective
  · intro i; exact smallRegs_injective.extend_apply _ _ _
  · intro i hi; exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i <;> simp_all [machine,tapes,parseStacks,Fin.exists_fin_succ]

theorem parseOld_eval (regs : Fin 8 → Bool) (a : Tape) (bits : List Bool)
    (hf : a.found = Encoding.frame bits) (hl : a.left = []) :
    ∃ rr, Eval parseOld (6 * bits.length + 4) (machine regs a)
      (machine rr { a with found := [], left := bits.reverse }) := by
  let d := SubexponentialSAT.SubexpRecordScan.recordState (regs ∘ smallRegs) a.found a.left [] [] [] []
  have he := SubexponentialSAT.SubexpRecordScan.parseFrame_eval d 0 1 (by decide) bits []
    (by simpa [d,SubexponentialSAT.SubexpRecordScan.recordState,SubexponentialSAT.SubexpRecordScan.storage] using hf)
  cases he with
  | call _ ht =>
    have hh := eval_call_lifted (SubexponentialSAT.SubexpRecordScan.parseFrame 0 1)
      parseRegisters parseStacks (machine regs a) smallRegs_injective parseStacks_injective ht
    have hb : SubexponentialSAT.SubexpRecordScan.afterFrame d 0 1 bits [] =
      SubexponentialSAT.SubexpRecordScan.recordState (readRegs (regs ∘ smallRegs) 0 1 (some false))
        [] bits.reverse [] [] [] [] := by
      apply congrArg (fun st => (⟨readRegs (regs ∘ smallRegs) 0 1 (some false), st⟩ : State 5 6))
      funext i; fin_cases i <;>
          simp [d,
            SubexponentialSAT.SubexpRecordScan.storage,hl]
    rw [hb] at hh
    change Eval parseOld _
      (embedState parseRegisters parseStacks (machine regs a)
        (SubexponentialSAT.SubexpRecordScan.recordState (regs ∘ smallRegs) a.found a.left [] [] [] [])) _ at hh
    rw [embed_parser,embed_parser,overlay_same] at hh
    have ha : { a with found := a.found, left := a.left } = a := by cases a; rfl
    rw [ha] at hh
    exact ⟨_,hh⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
