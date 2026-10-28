import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateProgram
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRouting

namespace OAI.Algorithms

/-! Lift the actual assignment and metadata selectors into the node state. -/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.ConstructivePacking

def WorkspaceEmpty (d : Data) : Prop :=
  ∀ i : Fin 288, 138 ≤ i.val → i.val ≤ 201 → d.stacks i = []

theorem factorPort_work : ∀ i : Fin 48, 7 ≤ i.val →
    138 ≤ (factorPort i).val ∧ (factorPort i).val ≤ 201 := by decide

theorem supportPort_work : ∀ i : Fin 64,
    i ≠ 0 → i ≠ 1 → i ≠ 30 → i ≠ 31 → i ≠ 32 → i ≠ 33 → i ≠ 38 →
      138 ≤ (supportPort i).val ∧ (supportPort i).val ≤ 201 := by decide

def routedBytes {r Q : ℕ} (t : Fin Q) (g : Fin r)
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) : Word :=
  Encoding.encodeList id (SubexpFactorRoutingTraversal.retained t g items)

def selectedSupport {D r Q Δ : ℕ}
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (g : ℕ) : Word :=
  Encoding.encodeList id
    (Subexp.SupportSelectionProgram.indexWords (Subexp.SupportSelectionProgram.colorTest P t g) D)

def selectedOutside {D r Q Δ : ℕ}
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ)) : Word :=
  Encoding.encodeList id
    (Subexp.SupportSelectionProgram.indexWords (Subexp.SupportSelectionProgram.outsideTest P) D)

theorem selectFactors_eval {r Q : ℕ} (t : Fin Q) (g : Fin r)
    (items : List (SubexpFactorRoutingTraversal.Item r Q)) (suffix : Word) (d : Data)
    (hwork : WorkspaceEmpty d) (h210 : d.stacks 210 = [])
    (h258 : d.stacks 258 = SubexpFactorRoutingTraversal.words items ++ suffix)
    (h225 : d.stacks 225 = Encoding.encodeList id (items.map Prod.snd))
    (h219 : CounterPrograms.value (d.stacks 219) = g.val)
    (h116 : d.stacks 116 = List.replicate t.val true)
    (h261 : d.stacks 261 = List.replicate r true)
    (h260 : (d.stacks 260).length = Q * r) :
    ∃ n e, n ≤ SubexpFactorRouting.runtime (projectState id factorPort d) t g items suffix ∧
      Eval selectFactors n d e ∧ e.regs = (fun _ => false) ∧
      e.stacks = Function.update d.stacks 210 (routedBytes t g items) := by
  let a := projectState id factorPort d
  have hc : SubexpFactorRoutingControl.Clean a := by
    intro i hi
    by_cases h6 : i = 6
    · subst i
      exact h210
    · have hi7 : 7 ≤ i.val := by
        have hn : i.val ≠ 6 := fun heq => h6 (Fin.ext heq)
        omega
      have hp := factorPort_work i hi7
      exact hwork (factorPort i) hp.1 hp.2
  obtain ⟨n, hn, ht⟩ := SubexpFactorRouting.program_runs t g items suffix a hc
    h258 h225 h219 h116 h261 h260
  let b := SubexpFactorRoutingControl.result a (routedBytes t g items)
  let e := embedState id factorPort d b
  refine ⟨n, e, hn, eval_call_from_state _ _ _ _ Function.injective_id factorPort_injective ht, ?_, ?_⟩
  · funext i
    simpa [e, b, SubexpFactorRoutingControl.result] using
      embedState_register id factorPort d b Function.injective_id i
  · change Function.extend factorPort
      (Function.update a.stacks 6 (routedBytes t g items)) d.stacks = _
    rw [ProgramLinking.extend_update factorPort_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project id factorPort d Function.injective_id factorPort_injective)
    change Function.extend factorPort a.stacks d.stacks = d.stacks at hp
    rw [hp]
    rfl

theorem selectSupport_eval {D r Q Δ : ℕ}
    (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (d : Data) (hwork : WorkspaceEmpty d)
    (h209 : d.stacks 209 = []) (h223 : d.stacks 223 = [])
    (h109 : d.stacks 109 = List.replicate D true)
    (h116 : d.stacks 116 = List.replicate t.val true)
    (h261 : d.stacks 261 = List.replicate r true)
    (h269 : d.stacks 269 = Subexp.SupportSelectionProgram.metadataTable P) :
    ∃ n e, n ≤ Subexp.SupportSelectionProgram.budget
        (Subexp.SupportSelectionProgram.metadataTable P).length D t.val r (d.stacks 219) ∧
      Eval selectSupport n d e ∧ e.regs = (fun _ => false) ∧
      e.stacks = Function.update
        (Function.update d.stacks 209 (selectedSupport P t (CounterPrograms.value (d.stacks 219))))
        223 (selectedOutside P) := by
  let a := projectState id supportPort d
  have ha : a = Subexp.SupportSelectionProgram.inputState d.regs
      (Subexp.SupportSelectionProgram.metadataTable P) D t.val r (d.stacks 219) := by
    apply state_ext
    · rfl
    · funext i
      by_cases h30 : i = 30
      · subst i
        simpa [a, projectState, supportPort, Subexp.SupportSelectionProgram.inputState,
          Subexp.SupportSelectionProgram.baseStacks] using h109
      by_cases h31 : i = 31
      · subst i
        rfl
      by_cases h32 : i = 32
      · subst i
        simpa [a, projectState, supportPort, Subexp.SupportSelectionProgram.inputState,
          Subexp.SupportSelectionProgram.baseStacks] using h116
      by_cases h33 : i = 33
      · subst i
        simpa [a, projectState, supportPort, Subexp.SupportSelectionProgram.inputState,
          Subexp.SupportSelectionProgram.baseStacks] using h269
      by_cases h38 : i = 38
      · subst i
        simpa [a, projectState, supportPort, Subexp.SupportSelectionProgram.inputState,
          Subexp.SupportSelectionProgram.baseStacks] using h261
      by_cases h0 : i = 0
      · subst i
        simpa [a, projectState, supportPort, Subexp.SupportSelectionProgram.inputState,
          Subexp.SupportSelectionProgram.baseStacks] using h209
      by_cases h1 : i = 1
      · subst i
        simpa [a, projectState, supportPort, Subexp.SupportSelectionProgram.inputState,
          Subexp.SupportSelectionProgram.baseStacks] using h223
      · have hp := supportPort_work i h0 h1 h30 h31 h32 h33 h38
        simpa [a, projectState, Subexp.SupportSelectionProgram.inputState,
          Subexp.SupportSelectionProgram.baseStacks, h30, h31, h32, h33, h38] using
          hwork (supportPort i) hp.1 hp.2
  obtain ⟨n, hn, ht⟩ := Subexp.SupportSelectionProgram.program_run P t (d.stacks 219) d.regs
  rw [← ha] at ht
  let b := Subexp.SupportSelectionProgram.outputState
    (Subexp.SupportSelectionProgram.metadataTable P) D t.val r (d.stacks 219)
    (selectedSupport P t (CounterPrograms.value (d.stacks 219))) (selectedOutside P)
  have hb : b.stacks = Function.update
      (Function.update a.stacks 0 (selectedSupport P t (CounterPrograms.value (d.stacks 219))))
      1 (selectedOutside P) := by
    rw [ha]
    rfl
  let e := embedState id supportPort d b
  refine ⟨n, e, hn, eval_call_from_state _ _ _ _ Function.injective_id supportPort_injective ht, ?_, ?_⟩
  · funext i
    simpa [e, b, Subexp.SupportSelectionProgram.outputState] using
      embedState_register id supportPort d b Function.injective_id i
  · change Function.extend supportPort b.stacks d.stacks = _
    rw [hb, ProgramLinking.extend_update supportPort_injective,
      ProgramLinking.extend_update supportPort_injective]
    have hp := congrArg StructuredProgram.State.stacks
      (embedState_project id supportPort d Function.injective_id supportPort_injective)
    change Function.extend supportPort a.stacks d.stacks = d.stacks at hp
    rw [hp]
    rfl

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
