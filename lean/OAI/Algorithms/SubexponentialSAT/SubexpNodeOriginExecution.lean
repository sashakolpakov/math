import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeOriginStage
import OAI.Algorithms.SubexponentialSAT.SubexpOriginExecution

namespace OAI.Algorithms

/-! The typed current-node cache executes through the fixed global origin
program. The native traversal and four-word residue arithmetic are invoked
by their proved execution theorem, rather than assumed as a callback. -/

namespace SubexponentialSAT.SubexpNodeOriginExecution

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpNodeOriginStage (Data localState)

variable (p μ : ℕ) [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)
variable (target : SubexpPreparedQuartic.Modulus p μ)
variable (reduction theta : SubexpTaylorRow.Code p μ)
variable (R N : ℕ) (hN : 0 < N)
variable (M : SubexpPreparedQuartic.Modulus p 1)
variable (width : List Bool) (hw : width.length = baseWidth p 1)

def output (es : List (List (SubexpTaylorRowCorrectness.RowExpr p))) : List Bool :=
  Encoding.encodeList (Encoding.encodeList SubexpFlatLift.encode)
    (SubexpOriginCacheSemantics.origins p μ source target reduction theta R N hN M width hw es)

theorem command_eval (hμ : 0 < μ) (inputWidth : List Bool)
    (hB : inputWidth.length = baseWidth p μ) (C : ℕ)
    (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
    (hC : ∀ incidence ∈ es, incidence.length ≤ C) (d : Data)
    (hi : SubexpOriginMap.incidenceInvariant M.bits inputWidth width (localState d))
    (hm : d.stacks 102 =
      SubexpOriginCacheSemantics.taylorBytes p μ source target reduction theta R N es)
    (h15 : d.stacks 153 = []) (h16 : d.stacks 154 = [])
    (h23 : d.stacks 161 = []) (h24 : d.stacks 227 = []) :
    ∃ n ≤ SubexpOriginMap.tableBound es.length C (baseWidth p μ) (baseWidth p 1)
        M.bits.length (N - 1), ∃ out : Data,
      Eval SubexpNodeOriginStage.command n d out ∧
      out.stacks = Function.update d.stacks 227
        (output p μ source target reduction theta R N hN M width hw es) := by
  obtain ⟨regs,n,hn,ht⟩ :=
    SubexpOriginExecution.program_runs p μ source target reduction theta R N hN M width hw
      hμ inputWidth hB C es hC (localState d) hi hm h15 h16 h23 h24
  let e : SubexpOriginControl.Data := ⟨regs, Function.update (localState d).stacks 24
    (output p μ source target reduction theta R N hN M width hw es)⟩
  have he := SubexpNodeOriginStage.command_eval_from_native d e n ht
  exact ⟨n,hn,embedState SubexpNodeOriginStage.registers SubexpNodeOriginStage.ports d e,
    he,SubexpNodeOriginStage.result_stacks d e _ rfl⟩

theorem program_runs (hμ : 0 < μ) (inputWidth : List Bool)
    (hB : inputWidth.length = baseWidth p μ) (C : ℕ)
    (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
    (hC : ∀ incidence ∈ es, incidence.length ≤ C) (d : Data)
    (hi : SubexpOriginMap.incidenceInvariant M.bits inputWidth width (localState d))
    (hm : d.stacks 102 =
      SubexpOriginCacheSemantics.taylorBytes p μ source target reduction theta R N es)
    (h15 : d.stacks 153 = []) (h16 : d.stacks 154 = [])
    (h23 : d.stacks 161 = []) (h24 : d.stacks 227 = []) :
    ∃ out : Data, RunsIn SubexpNodeOriginStage.program
        (SubexpOriginMap.tableBound es.length C (baseWidth p μ) (baseWidth p 1)
          M.bits.length (N - 1))
        (d.withPC (some SubexpNodeOriginStage.program.entry)) (out.withPC none) ∧
      out.stacks = Function.update d.stacks 227
        (output p μ source target reduction theta R N hN M width hw es) := by
  obtain ⟨n,hn,out,he,hs⟩ := command_eval p μ source target reduction theta R N hN M width hw
    hμ inputWidth hB C es hC d hi hm h15 h16 h23 h24
  refine ⟨out,⟨n,hn,?_⟩,hs⟩
  cases he with
  | call _ ht => exact ht

end SubexponentialSAT.SubexpNodeOriginExecution

end OAI.Algorithms
