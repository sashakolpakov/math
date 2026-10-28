import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramEntry

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open IdempotentTableEntryProgram (codeBits outputPort entryCode)

abbrev prepareEntry : Cmd 8 41 :=
  .seq (.call (StackRoutines.copyProgram 25 0 4 (0 : Fin 8) 1)) <|
  .seq (.call (StackRoutines.copyProgram 26 1 4 (0 : Fin 8) 1))
    (.call (StackRoutines.copyProgram 24 2 4 (0 : Fin 8) 1))

abbrev entryCommand : Cmd 8 41 :=
  .seq prepareEntry (.seq selector (.seq dispatchEntry (.seq (clearAt 2) (clearAt 3))))

theorem prepareEntry_eval (d : Data)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = []) (h4 : d.stacks 4 = []) :
    ∃ rf, Eval prepareEntry
      (7*((d.stacks 25).length+(d.stacks 26).length+(d.stacks 24).length)+15) d
      ⟨rf,Function.update (Function.update (Function.update d.stacks
        0 (d.stacks 25)) 1 (d.stacks 26)) 2 (d.stacks 24)⟩ := by
  let a := afterCopy d 25 0 0 1
  let b := afterCopy a 26 1 0 1
  have ha := copy_eval d 25 0 4 0 1 (by decide) (by decide) (by decide) (by decide) h4
  have hb := copy_eval a 26 1 4 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [a,afterCopy,StackRoutines.copyStacks,h4])
  have hc := copy_eval b 24 2 4 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [b,a,afterCopy,StackRoutines.copyStacks,h4])
  have he := ha.seq (hb.seq hc)
  refine ⟨(afterCopy b 24 2 0 1).regs,?_⟩
  convert he using 1 <;>
    simp [b,a,afterCopy,StackRoutines.copyStacks,h0,h1,h2] ; ring

theorem entryCommand_eval (d : Data) (i j k : ℕ)
    (hi : d.stacks 25 = List.replicate i true)
    (hj : d.stacks 26 = List.replicate j true)
    (hk : d.stacks 24 = List.replicate k true)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = []) (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) :
    ∃ n rf, n ≤ 49*(i+j+k)+7*(d.stacks (entrySource (entryCode i j k))).length+69 ∧
      Eval entryCommand n d ⟨rf,Function.update d.stacks 22
        (d.stacks (entrySource (entryCode i j k)) ++ d.stacks 22)⟩ := by
  obtain ⟨ra,ha⟩ := prepareEntry_eval d h0 h1 h2 h4
  let a : Data := ⟨ra,Function.update (Function.update (Function.update d.stacks
    0 (d.stacks 25)) 1 (d.stacks 26)) 2 (d.stacks 24)⟩
  obtain ⟨ns,rs,zs,bs,hns,hsize,hs,hcode⟩ := selector_eval a i j k
    (by simp [a,hi]) (by simp [a,hj]) (by simp [a,hk]) (by simp [a,h3])
  let b : Data := ⟨rs,Function.update (Function.update (Function.update (Function.update a.stacks
    0 []) 1 []) 2 zs) 3 bs⟩
  obtain ⟨nc,rc,hnc,hc⟩ := dispatchEntry_eval b (entryCode i j k)
    (by simp [b,a,h4]) hcode
  let c : Data := ⟨rc,Function.update b.stacks 22
    (b.stacks (entrySource (entryCode i j k)) ++ b.stacks 22)⟩
  have hsource : b.stacks (entrySource (entryCode i j k)) =
      d.stacks (entrySource (entryCode i j k)) := by
    generalize entryCode i j k = code
    fin_cases code <;> simp [b,a,entrySource]
  have htwo := clearAt_eval c 2
  let e := clearResult c 2
  have hthree := clearAt_eval e 3
  have hout : (clearResult e 3).stacks = Function.update d.stacks 22
      (d.stacks (entrySource (entryCode i j k)) ++ d.stacks 22) := by
    simp only [e,clearResult,c,hsource]
    funext p
    by_cases hp22 : p = 22
    · subst p; simp [b,a]
    · by_cases hp0 : p = 0
      · subst p; simp [b,a,h0]
      · by_cases hp1 : p = 1
        · subst p; simp [b,a,h1]
        · by_cases hp2 : p = 2
          · subst p; simp [h2]
          · by_cases hp3 : p = 3
            · subst p; simp [h3]
            · simp [b,a,hp22,hp0,hp1,hp2,hp3]
  have hf : clearResult e 3 = ⟨(clearResult e 3).regs,Function.update d.stacks 22
      (d.stacks (entrySource (entryCode i j k)) ++ d.stacks 22)⟩ := state_ext rfl hout
  have he := ha.seq (hs.seq (hc.seq (htwo.seq hthree)))
  rw [hf] at he
  refine ⟨_,_,?_,he⟩
  have hc2 : (c.stacks 2).length = zs.length := by simp [c,b]
  have he3 : (e.stacks 3).length = bs.length := by simp [e,clearResult,c,b]
  simp only [hsource] at hnc
  simp only [hi,hj,hk,List.length_replicate,hc2,he3]
  omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
