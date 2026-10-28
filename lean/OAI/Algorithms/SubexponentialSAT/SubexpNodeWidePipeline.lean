import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWideExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheStage
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplateStage
import OAI.Algorithms.SubexponentialSAT.SubexpNodeStageCopies
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentPipeline
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceHost
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# The node worker with concrete cache, source, jobs and moment tables

The only program still supplied here is the current-node basis/bank/packet
assembler. It must read the actual static masters and cache and write the
raw blueprint on 15. Every other call below is an installed finite program.
The trace lemma is compositional; it does not discharge the assembler's
execution contract or the remaining producer-to-consumer data equalities.
-/

namespace SubexponentialSAT.SubexpNodeWidePipeline

open BitProgram StructuredCalls
open SubexpNodeWideLoop (Stage LocalData)

abbrev call256 {l : ℕ} (p : Program 16 256 l) : Cmd 16 288 :=
  .call (ProgramLinking.liftProgram p id (Fin.castAdd 32))

abbrev lift256 (c : Cmd 16 256) (input output : Fin 256) : Cmd 16 288 :=
  liftCommand c input output id (Fin.castAdd 32)

abbrev cache : Cmd 16 288 := call256 SubexpNodeCacheStage.program
abbrev index : Cmd 16 288 := call256 SubexpNodeIndexProgram.program
abbrev templateMetadata : Cmd 16 288 := lift256 SubexpNodeStageCopies.prepareTemplate 128 204
abbrev template : Cmd 16 288 := call256 SubexpNodeTemplateStage.program
abbrev clearTemplate : Cmd 16 288 := lift256 SubexpNodeStageCopies.clearTemplate 204 204
abbrev jobMetadata : Cmd 16 288 := lift256 SubexpNodeStageCopies.prepareJobs 109 140
abbrev jobs : Cmd 16 288 :=
  call256 (SubexpNodeJobsStage.masterProgram SubexpMomentSourceHost.fixedCommand)
abbrev clearJobs : Cmd 16 288 := lift256 SubexpNodeStageCopies.clearJobs 200 200
abbrev phase : Cmd 16 288 := call256 SubexpNodeMomentPipeline.phaseProgram

/-- The current-node index is computed before the raw blueprint assembler.
The cache is consumed and cleared before the job stream occupies port 100. -/
abbrev command (blueprint : Stage) : Cmd 16 288 :=
  .seq cache (.seq index (.seq (.call blueprint.program)
    (.seq templateMetadata (.seq template (.seq clearTemplate
      (.seq jobMetadata (.seq jobs (.seq clearJobs phase))))))))

abbrev worker (blueprint : Stage) : Program 16 288 (size (command blueprint) + 1) :=
  compiled (command blueprint) 78 102

noncomputable abbrev program (blueprint : Stage) :
    Program 16 352 (size (SubexpNodeWideLoop.command (worker blueprint)) + 1) :=
  @SubexpNodeWideLoop.program (size (command blueprint) + 1) (worker blueprint)

/-- All ten component executions are executions of their actual fixed
tables. The sum counts each component and the worker's final halt. -/
theorem worker_trace (blueprint : Stage)
    {n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 : ℕ}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 : LocalData}
    (h0 : Eval cache n0 d0 d1)
    (h1 : Eval index n1 d1 d2)
    (h2 : Trace blueprint.program n2
      (d2.withPC (some blueprint.program.entry)) (d3.withPC none))
    (h3 : Eval templateMetadata n3 d3 d4)
    (h4 : Eval template n4 d4 d5)
    (h5 : Eval clearTemplate n5 d5 d6)
    (h6 : Eval jobMetadata n6 d6 d7)
    (h7 : Eval jobs n7 d7 d8)
    (h8 : Eval clearJobs n8 d8 d9)
    (h9 : Eval phase n9 d9 d10) :
    Trace (worker blueprint)
      (n0 + (n1 + (n2 + (n3 + (n4 + (n5 + (n6 + (n7 + (n8 + n9)))))))) + 1)
      (d0.withPC (some (worker blueprint).entry)) (d10.withPC none) := by
  exact compiled_halt_trace
    (h0.seq (h1.seq ((Eval.call blueprint.program h2).seq
      (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9))))))))) 78 102

end SubexponentialSAT.SubexpNodeWidePipeline

end OAI.Algorithms
