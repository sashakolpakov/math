import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Native frame and list movement for the moment-assembly driver. The fixed
machine has the node worker's 40-register/768-stack size. The arithmetic core
uses stacks below 56; assignment/head/support/bucket streams live on 160+.
All payload lengths and iteration counts are runtime data. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

/-- A raw list of framed records. The enclosing frame supplies its boundary. -/
def rawFrames : List (List Bool) → List Bool
  | [] => []
  | x :: xs => Encoding.frame x ++ rawFrames xs

@[simp] theorem rawFrames_nil : rawFrames [] = [] := rfl
@[simp] theorem rawFrames_cons (x : List Bool) (xs : List (List Bool)) :
    rawFrames (x :: xs) = Encoding.frame x ++ rawFrames xs := rfl

theorem rawFrames_cons_ne (x : List Bool) (xs : List (List Bool)) :
    rawFrames (x :: xs) ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp [rawFrames] at hh

abbrev clear (src : Fin 768) : Code := .call (clearProgram src 0 1)
abbrev copy (src dst : Fin 768) : Code := .call (copyProgram src dst 179 0 1)
abbrev transfer (src dst : Fin 768) : Code := .call (transferProgram src dst 0 1)

abbrev afterClear (d : Data) (src : Fin 768) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩
abbrev afterCopy (d : Data) (src dst : Fin 768) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩
abbrev afterTransfer (d : Data) (src dst : Fin 768) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

theorem clear_eval (d : Data) (src : Fin 768) :
    Eval (clear src) (2*(d.stacks src).length+3) d (afterClear d src) :=
  .call _ (ListRegisterProgram.clear_run src 0 1 d.regs d.stacks)

theorem copy_eval (d : Data) (src dst : Fin 768)
    (hsd : src ≠ dst) (hst : src ≠ 179) (htd : (179 : Fin 768) ≠ dst)
    (ht : d.stacks 179 = []) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (afterCopy d src dst) :=
  .call _ (ListRegisterProgram.copy_run src dst 179 0 1 hsd hst htd (by decide)
    d.regs d.stacks ht)

theorem transfer_eval (d : Data) (src dst : Fin 768) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(d.stacks src).length+3) d (afterTransfer d src dst) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide) d.regs d.stacks)

def framePorts (src dst : Fin 768) (hsd : src ≠ dst) : RecordPrograms.Ports 40 768 where
  tag := 0
  present := 1
  found := 2
  source := src
  payload := dst
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := hsd

abbrev readFrame (src dst : Fin 768) (hsd : src ≠ dst) : Code :=
  RecordPrograms.reader (framePorts src dst hsd)

abbrev afterFrame (d : Data) (src dst : Fin 768) (bits tail : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src tail) dst (bits.reverse ++ d.stacks dst)⟩

theorem readFrame_eval (d : Data) (src dst : Fin 768) (hsd : src ≠ dst)
    (bits tail : List Bool) (hs : d.stacks src = Encoding.frame bits ++ tail) :
    Eval (readFrame src dst hsd) (6*bits.length+4) d (afterFrame d src dst bits tail) := by
  let ports := framePorts src dst hsd
  have h := RecordPrograms.reader_eval ports d bits tail (d.stacks dst)
    (d.regs 0) (d.regs 1) (d.regs 2)
  have hi : RecordPrograms.state ports d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) (d.stacks dst) = d :=
    RecordPrograms.state_eq_self ports d _ _ _ _ _ rfl rfl rfl hs rfl
  rw [hi] at h
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [ ports, framePorts, readRegs]
  · funext i
    simp [ ports, framePorts ]

/-- A frame is read into a reverse buffer and then physically moved forward. -/
abbrev takeFrame (src dst : Fin 768) (hs : src ≠ 164) : Code :=
  .seq (readFrame src 164 hs) (transfer 164 dst)

abbrev afterTake (d : Data) (src dst : Fin 768) (bits tail : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update (Function.update d.stacks src tail) dst bits⟩

theorem takeFrame_eval (d : Data) (src dst : Fin 768)
    (hs : src ≠ 164) (hd : (164 : Fin 768) ≠ dst) (hsd : src ≠ dst)
    (bits tail : List Bool) (hsrc : d.stacks src = Encoding.frame bits ++ tail)
    (ht : d.stacks 164 = []) (hout : d.stacks dst = []) :
    Eval (takeFrame src dst hs) (9*bits.length+7) d (afterTake d src dst bits tail) := by
  have h1 := readFrame_eval d src 164 hs bits tail hsrc
  have h2 := transfer_eval (afterFrame d src 164 bits tail) 164 dst hd
  have he := h1.seq h2
  convert he using 1
  · simp [ ht]
    omega
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ readRegs]
    · funext i
      by_cases hi : i = src
      · subst i
        simp [ transferStacks, hs, hsd, Ne.symm hd, Ne.symm hsd, ht, hout]
      by_cases hj : i = dst
      · subst i
        simp [ transferStacks, Ne.symm hd, Ne.symm hsd, ht, hout]
      by_cases hk : i = 164
      · subst i
        simp [ transferStacks, hd,
          Ne.symm hs, Ne.symm hd, Ne.symm hsd, ht, hout]
      simp [ transferStacks, hi, hj, hk]

abbrev peek (src : Fin 768) : Code := .base (.atom (.peek src 0 15))
abbrev afterPeek (d : Data) (src : Fin 768) : Data :=
  ⟨readRegs d.regs 0 15 (d.stacks src).head?, d.stacks⟩

theorem peek_eval (d : Data) (src : Fin 768) :
    Eval (peek src) 1 d (afterPeek d src) := .base (.atom _ _)

abbrev rawLoop (src : Fin 768) (body : Code) : Code := .while 15 (.seq body (peek src))
abbrev rawScan (src : Fin 768) (body : Code) : Code := .seq (peek src) (rawLoop src body)

theorem peek_empty (d : Data) (src : Fin 768) (h : d.stacks src = []) :
    (afterPeek d src).regs 15 = false := by simp [ h, readRegs]

theorem peek_nonempty (d : Data) (src : Fin 768) (h : d.stacks src ≠ []) :
    (afterPeek d src).regs 15 = true := by
  cases he : d.stacks src with
  | nil => exact False.elim (h he)
  | cons b bs => simp [ he, readRegs]

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
