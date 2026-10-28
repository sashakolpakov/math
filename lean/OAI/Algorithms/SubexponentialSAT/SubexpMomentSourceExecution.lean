import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceBlocks

namespace OAI.Algorithms

/-! Current-X construction of the weighted block stream from a reusable,
unweighted template. Every output weight has an actual arithmetic trace. -/

namespace SubexponentialSAT.SubexpMomentSourceProgram

open BitProgram StructuredCalls

attribute [local irreducible] WeightResult.literal TermResult.prepared BlockResult.prepared

def preparedBlocks {ctx : Context} {a : Fin ctx.dimension → ℕ}
    (outs : List (BlockResult ctx a)) : List SubexpBlockAssembly.Block :=
  outs.map BlockResult.prepared

def preparationBudget (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (bs : List (BlockData ctx)) (outs : List (BlockResult ctx a)) : ℕ :=
  7*ctx.template.length +
    scanSteps (fun b => encodeBlock b.template) (blockBudget ctx a) bs outs +
    3*(SubexpBlockAssembly.encodeBlocks (preparedBlocks outs)).length+19

theorem copyTemplate_eval (ctx : Context) (r : Fin 8 → Bool) (captured : Word) :
    Eval (.call (StackRoutines.copyProgram 62 58 2 (0 : Fin 8) 1))
      (7*ctx.template.length+5)
      (state ctx r [] SubexpBlockAssembly.emptyBuffers [] [] [] captured)
      (state ctx (readRegs r 0 1 none) ctx.template SubexpBlockAssembly.emptyBuffers [] [] [] captured) := by
  let d := state ctx r [] SubexpBlockAssembly.emptyBuffers [] [] [] captured
  have h : Eval (.call (StackRoutines.copyProgram 62 58 2 (0 : Fin 8) 1))
      (7*ctx.template.length+5) d
      ⟨readRegs d.regs 0 1 none,StackRoutines.copyStacks 62 58 d.stacks⟩ :=
    .call _ (ListRegisterProgram.copy_run 62 58 2 0 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks rfl)
  have he : (⟨readRegs d.regs 0 1 none,StackRoutines.copyStacks 62 58 d.stacks⟩ : Data) =
      state ctx (readRegs r 0 1 none) ctx.template SubexpBlockAssembly.emptyBuffers [] [] [] captured := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> first | rfl | exact List.append_nil ctx.template
  simpa only [he] using h

theorem prepareBlocks_eval (ctx : Context) (a : Fin ctx.dimension → ℕ)
    (hc : ContextGood ctx a) (bs : List (BlockData ctx))
    (hTemplate : ctx.template = encodeTemplate (bs.map BlockData.template))
    (r : Fin 8 → Bool) (captured : Word) :
    ∃ (outs : List (BlockResult ctx a)) (n : ℕ) (rf : Fin 8 → Bool),
      List.Forall₂ (fun b out => out.input = b) bs outs ∧
      n ≤ preparationBudget ctx a bs outs ∧
      Eval prepareBlocks n
        (state ctx r [] SubexpBlockAssembly.emptyBuffers [] [] [] captured)
        (state ctx (flags rf false false false)
          (SubexpBlockAssembly.encodeBlocks (preparedBlocks outs))
          SubexpBlockAssembly.emptyBuffers [] [] [] captured) := by
  have hcopy := copyTemplate_eval ctx r captured
  let update := fun (out : BlockResult ctx a) (acc : SubexpBlockAssembly.Buffers) =>
    SubexpBlockAssembly.emit 5
      (SubexpBlockAssembly.record (SubexpBlockAssembly.encodeBlock out.prepared)) acc
  let inv := fun acc : SubexpBlockAssembly.Buffers =>
    acc 2 = [] ∧ acc 3 = [] ∧ acc 4 = [] ∧ acc 6 = []
  obtain ⟨outs,ns,rs,houts,hns,hs⟩ := scan_relational ctx blockBody
    (fun b => encodeBlock (BlockData.template b)) (blockBudget ctx a)
    (fun b out => out.input = b) update inv
    (fun b r rest captured acc hacc => blockBody_eval ctx a hc b r rest captured acc
      hacc.1 hacc.2.1 hacc.2.2.1 hacc.2.2.2)
    (by intro b out acc hb hacc; simpa [inv,update,SubexpBlockAssembly.emit] using hacc)
    bs (readRegs r 0 1 none) [] captured SubexpBlockAssembly.emptyBuffers
    (by simp [inv,SubexpBlockAssembly.emptyBuffers])
  have htemplate : Encoding.encodeList (fun b => encodeBlock (BlockData.template b)) bs = ctx.template := by
    rw [hTemplate,encodeTemplate,encodeList_map]
  rw [List.append_nil,htemplate] at hs
  let records := (outs.map (fun out =>
    SubexpBlockAssembly.record (SubexpBlockAssembly.encodeBlock out.prepared))).flatten
  let pending := SubexpBlockAssembly.emit 5 records SubexpBlockAssembly.emptyBuffers
  have hfold : outs.foldl (fun acc out => update out acc) SubexpBlockAssembly.emptyBuffers = pending :=
    SubexpBlockAssembly.fold_emit 5
      (fun out => SubexpBlockAssembly.record (SubexpBlockAssembly.encodeBlock out.prepared))
      outs SubexpBlockAssembly.emptyBuffers
  rw [hfold] at hs
  let ready := Function.update pending 5 (false :: pending 5)
  let r1 := flags rs false (rs 1) (rs 2)
  let r2 := flags r1 false false (r1 2)
  have hp := base_eval ctx rs [] [] pending ready [] [] [] [] captured false (rs 1) (rs 2)
    (SubexpBlockAssembly.pushBuffer_measured 5 false (rs 0) (rs 1) (rs 2) [] ctx.zero ctx.one pending)
  have hready : Function.update ready 5 [] = SubexpBlockAssembly.emptyBuffers := by
    funext i
    by_cases hi : i = 5
    · subst i
      rfl
    · simp only [ready,pending,SubexpBlockAssembly.emit,Function.update_of_ne hi]
  have hbytes : (ready 5).reverse = SubexpBlockAssembly.encodeBlocks (preparedBlocks outs) := by
    rw [SubexpBlockAssembly.encodeBlocks,SubexpBlockAssembly.encodeList_eq_records]
    simp [ready,pending,records,preparedBlocks,SubexpBlockAssembly.emit,
      SubexpBlockAssembly.emptyBuffers,List.reverse_cons,List.map_map,Function.comp_def]
  have htLocal := SubexpBlockAssembly.measured_result
    (SubexpBlockAssembly.transfer_eval 18 0 (by decide)
      (SubexpBlockAssembly.state (r1 0) (r1 1) (r1 2) [] ctx.zero ctx.one ready))
    (SubexpBlockAssembly.transferOutput_work (r1 0) (r1 1) (r1 2) ctx.zero ctx.one ready)
  change Eval _ (3*(ready 5).length+3) _ _ at htLocal
  rw [hready,hbytes] at htLocal
  have ht := base_eval ctx r1 [] (SubexpBlockAssembly.encodeBlocks (preparedBlocks outs))
    ready SubexpBlockAssembly.emptyBuffers [] [] [] [] captured false false (r1 2) htLocal
  have hr := base_eval ctx r2 (SubexpBlockAssembly.encodeBlocks (preparedBlocks outs))
    (SubexpBlockAssembly.encodeBlocks (preparedBlocks outs))
    SubexpBlockAssembly.emptyBuffers SubexpBlockAssembly.emptyBuffers [] [] [] [] captured false false false
    (SubexpBlockAssembly.reset_measured (r2 0) (r2 1) (r2 2)
      (SubexpBlockAssembly.encodeBlocks (preparedBlocks outs)) ctx.zero ctx.one [] SubexpBlockAssembly.emptyBuffers)
  have h := Eval.seq hcopy (Eval.seq hs (Eval.seq hp (Eval.seq ht hr)))
  refine ⟨outs,_,r2,houts,?_,h⟩
  have hlen : (ready 5).length = (SubexpBlockAssembly.encodeBlocks (preparedBlocks outs)).length := by
    rw [←hbytes,List.length_reverse]
  unfold preparationBudget
  rw [hlen]
  omega

end SubexponentialSAT.SubexpMomentSourceProgram

end OAI.Algorithms
