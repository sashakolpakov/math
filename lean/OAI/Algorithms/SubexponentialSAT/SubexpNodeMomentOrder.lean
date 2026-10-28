import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNodeLiftData

namespace OAI.Algorithms

/-! The physical node collector follows the actual finite-field node order. -/

namespace SubexponentialSAT.SubexpNodeMomentOrder

open BitProgram StructuredCalls SubexpNodeMomentLoop

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)

noncomputable def nodeWord (hμ : 0 < μ) (i : Fin (p^4 - 1)) : List Bool :=
  SubexpQuarticEncoding.encodeSelected p μ hμ
    (SubexpActualRing.sectionValue p μ hμ (SubexpMachineNodeOrder.nodeEquiv p i).val)

theorem liftedNodeWords_eq (hμ : 0 < μ) :
    SubexpNodeLiftData.liftedNodeWords p μ M = List.ofFn (nodeWord p μ hμ) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hiq : i < p^4 - 1 := by simpa using hi
    simpa only [nodeWord, List.get_eq_getElem, List.getElem_ofFn] using
      SubexpNodeLiftData.liftedNodeWords_get p μ M hμ ⟨i, hiq⟩

/-- This is the actual collector instantiated with the generated node table.
The local finite worker's trace contract remains explicit; no per-node jet
is supplied to the machine as input. -/
theorem program_runs {l : ℕ} (worker : Program 16 256 l)
    (workspace : LocalStore → Prop) (shape : List Bool)
    (jet : List Bool → List Bool) (cost : List Bool → ℕ)
    (contract : NodeContract worker
      (fun bits => bits ∈ SubexpNodeLiftData.liftedNodeWords p μ M)
      workspace shape jet cost)
    (hμ : 0 < μ) (d : Data) (hr : Ready workspace d)
    (hm : d.stacks 300 = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p μ M))
    (h301 : d.stacks 301 = []) (h302 : d.stacks 302 = [])
    (h303 : d.stacks 303 = []) (h304 : d.stacks 304 = [])
    (h256 : d.stacks 256 = []) (h265 : d.stacks 265 = []) :
    ∃ out : Data,
      RunsIn (SubexpNodeMomentLoop.program worker)
        (totalCost cost shape jet (SubexpNodeLiftData.liftedNodeWords p μ M) + 1)
        (d.withPC (some (SubexpNodeMomentLoop.program worker).entry)) (out.withPC none) ∧
      Ready workspace out ∧
      out.stacks 256 = (List.ofFn (nodeWord p μ hμ)).flatten ∧
      out.stacks 265 = (List.ofFn (fun i => jet (nodeWord p μ hμ i))).flatten ∧
      out.stacks 300 = d.stacks 300 ∧
      out.stacks 301 = [] ∧ out.stacks 302 = [] ∧
      out.stacks 303 = [] ∧ out.stacks 304 = [] ∧
      (∀ i : Fin 256, SourceBank i → out.stacks (localPorts i) = d.stacks (localPorts i)) := by
  obtain ⟨n, hn, out, he, ho, hnodes, hjets, hmaster, hs1, hs2, hs3, hs4, hf⟩ :=
    SubexpNodeMomentLoop.command_eval worker _ workspace shape jet cost contract
      (SubexpNodeLiftData.liftedNodeWords p μ M) d (fun _ h => h) hr hm
      h301 h302 h303 h304 h256 h265
  refine ⟨out, SubexpNodeMomentLoop.program_runs worker he hn, ho, ?_, ?_,
    hmaster, hs1, hs2, hs3, hs4, hf⟩
  · simpa only [liftedNodeWords_eq p μ M hμ] using hnodes
  · simpa only [liftedNodeWords_eq p μ M hμ, List.map_ofFn, Function.comp_def] using hjets

end SubexponentialSAT.SubexpNodeMomentOrder

end OAI.Algorithms
