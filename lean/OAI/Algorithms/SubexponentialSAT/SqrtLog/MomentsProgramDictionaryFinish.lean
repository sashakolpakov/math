import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryReplace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramDictionaryMoves

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev finish : Cmd 8 27 := .seq (clear 18)
  (.seq (transfer 0 26) (.seq replace (.seq (copy 25 15 23) (clear 25))))

def updatedBytes (entries : List (List Bool × List Bool)) (query coeff : List Bool) : List Bool :=
  Squarefree.Program.rawEntries ((query,coeff)::(Squarefree.Program.erasedEntries query entries).reverse)

def finishBudget (entries : List (List Bool × List Bool)) (query coeff remain : List Bool) : ℕ :=
  2 * remain.length + 7 * coeff.length + Squarefree.Program.eraseBudget query entries +
  4 * query.length + 9 * (updatedBytes entries query coeff).length + 31

theorem finish_eval (regs : Fin 8 → Bool) (a : Tape)
    (entries : List (List Bool × List Bool)) (query coeff : List Bool)
    (hd : a.dict = Squarefree.Program.rawEntries entries) (hq : a.query = query.reverse)
    (ho : a.out = coeff) (hc : a.combined = []) (hr : a.result = []) :
    ∃ n ≤ finishBudget entries query coeff a.remain, ∃ rr,
      Eval finish n (machine regs a)
        (machine rr { a with dict := updatedBytes entries query coeff, query := [], remain := [], out := [], combined := [], result := [] }) := by
  let a1 : Tape := { a with remain := [] }
  let a2 : Tape := { a1 with out := [], combined := a1.out.reverse }
  let output := updatedBytes entries query coeff
  let a3 : Tape := { a2 with dict := [], query := [], result := output, combined := [] }
  let a4 : Tape := { a3 with dict := a3.result }
  let a5 : Tape := { a4 with result := [] }
  have hclear := clearRemain_eval regs a
  have htransfer := transferSum_eval (readRegs regs 0 1 none) a1 hc
  obtain ⟨n,hn,rr,hreplace⟩ := replace_eval
    (readRegs (readRegs regs 0 1 none) 0 1 none) a2 entries query coeff hd hq
    (by simp [a2,a1,ho]) rfl hr
  let r3 := overlay (readRegs (readRegs regs 0 1 none) 0 1 none) rr
  have hcopy := copyResult_eval r3 a3 rfl
  have hclean := clearResult_eval (readRegs r3 0 1 none) a4
  have run := hclear.seq (htransfer.seq (hreplace.seq (hcopy.seq hclean)))
  refine ⟨_, ?_, readRegs (readRegs r3 0 1 none) 0 1 none, (by simpa only [finish,a1,a2,a3,a4,a5,output,r3,updatedBytes] using run)⟩
  simp only [ho] at hn ⊢
  dsimp [finishBudget,updatedBytes]
  omega

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
