import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWideExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentOrder

namespace OAI.Algorithms

/-! The wider collector keeps the same generated node order and frames all static inputs. -/

namespace SubexponentialSAT.SubexpNodeWideOrder

open BitProgram StructuredCalls SubexpNodeWideLoop
open SubexpNodeMomentOrder (nodeWord liftedNodeWords_eq)

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)

/-- This is an actual finite collector. Its remaining contract is the
execution of the installed per-node table, including its static-data frame. -/
theorem program_runs {l : ℕ} (worker : Program 16 288 l)
    (workspace : LocalStore → Prop) (shape : List Bool)
    (jet : List Bool → List Bool) (cost : List Bool → ℕ)
    (contract : NodeContract worker
      (fun bits => bits ∈ SubexpNodeLiftData.liftedNodeWords p μ M)
      workspace shape jet cost)
    (hμ : 0 < μ) (d : Data) (hr : Ready workspace d)
    (hm : d.stacks 332 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p μ M))
    (h333 : d.stacks 333 = []) (h334 : d.stacks 334 = [])
    (h335 : d.stacks 335 = []) (h336 : d.stacks 336 = [])
    (h288 : d.stacks 288 = []) (h297 : d.stacks 297 = []) :
    ∃ out : Data,
      RunsIn (SubexpNodeWideLoop.program worker)
        (totalCost cost shape jet (SubexpNodeLiftData.liftedNodeWords p μ M) + 1)
        (d.withPC (some (SubexpNodeWideLoop.program worker).entry)) (out.withPC none) ∧
      Ready workspace out ∧
      out.stacks 288 = (List.ofFn (nodeWord p μ hμ)).flatten ∧
      out.stacks 297 = (List.ofFn (fun i => jet (nodeWord p μ hμ i))).flatten ∧
      out.stacks 332 = d.stacks 332 ∧
      out.stacks 333 = [] ∧ out.stacks 334 = [] ∧
      out.stacks 335 = [] ∧ out.stacks 336 = [] ∧
      (∀ i : Fin 288, ProtectedBank i →
        out.stacks (localPorts i) = d.stacks (localPorts i)) := by
  obtain ⟨n, hn, out, he, ho, hnodes, hjets, hmaster, hs1, hs2, hs3, hs4, hf⟩ :=
    SubexpNodeWideLoop.command_eval worker _ workspace shape jet cost contract
      (SubexpNodeLiftData.liftedNodeWords p μ M) d (fun _ h => h) hr hm
      h333 h334 h335 h336 h288 h297
  refine ⟨out, SubexpNodeWideLoop.program_runs worker he hn, ho, ?_, ?_,
    hmaster, hs1, hs2, hs3, hs4, hf⟩
  · simpa only [liftedNodeWords_eq p μ M hμ] using hnodes
  · simpa only [liftedNodeWords_eq p μ M hμ, List.map_ofFn, Function.comp_def] using hjets

end SubexponentialSAT.SubexpNodeWideOrder

end OAI.Algorithms
