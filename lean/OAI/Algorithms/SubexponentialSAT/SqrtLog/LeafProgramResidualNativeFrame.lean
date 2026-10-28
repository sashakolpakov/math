import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidual
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCountCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWorkspace

namespace OAI.Algorithms

/-! Physical frame lemmas for the fixed residual program. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def collectorPorts : List (Fin 768) := [301,302,303,304,305,307,78,102,104,256,265]
def collectorBlankPorts : List (Fin 768) := [301,302,303,304,305,307,78,102,104,265]

theorem collector_frame (s : LeafNodeSamplesProgram.Store) (i : Fin 768)
    (hi : i ∉ collectorPorts) : LeafNodeSamplesProgram.tapes s i=s.frame i := by
  simp only [collectorPorts,List.mem_cons,List.mem_nil_iff,or_false,not_or] at hi
  simp only [LeafNodeSamplesProgram.tapes,ite_eq_right hi.1,ite_eq_right hi.2.1,
    ite_eq_right hi.2.2.1,ite_eq_right hi.2.2.2.1,ite_eq_right hi.2.2.2.2.1,
    ite_eq_right hi.2.2.2.2.2.1,ite_eq_right hi.2.2.2.2.2.2.1,
    ite_eq_right hi.2.2.2.2.2.2.2.1,ite_eq_right hi.2.2.2.2.2.2.2.2.1,
    ite_eq_right hi.2.2.2.2.2.2.2.2.2.1,ite_eq_right hi.2.2.2.2.2.2.2.2.2.2]

theorem collector_initial (a : Data)
    (he : ∀ i∈collectorBlankPorts,a.stacks i=[]) :
    LeafNodeSamplesProgram.state a.regs
      (LeafNodeSamplesProgram.initial a.stacks (a.stacks 256))=a := by
  apply congrArg (StructuredProgram.State.mk a.regs)
  funext i
  by_cases hb : i ∈ collectorBlankPorts
  · have hz := he i hb
    simp only [collectorBlankPorts,List.mem_cons,List.mem_nil_iff,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simpa [LeafNodeSamplesProgram.initial,LeafNodeSamplesProgram.tapes] using hz.symm
  · by_cases hn : i=256
    · subst i
      simp [LeafNodeSamplesProgram.initial,LeafNodeSamplesProgram.tapes]
    · apply collector_frame
      simpa [collectorPorts,collectorBlankPorts,hn] using hb

theorem protected_collector (i : Fin 768) (hi : Query.Protected i) :
    i ∉ collectorPorts := by
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hi
  all_goals try decide
  intro hm
  simp only [collectorPorts,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem protected_high (i : Fin 768) (hi : Query.Protected i) :
    i ∉ LeafHighContextProgram.changed := by
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hi
  all_goals try decide
  intro hm
  simp only [LeafHighContextProgram.changed,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem prepare_protected (a : Data) (i : Fin 768) (hi : Query.Protected i)
    (ho : i≠323) : (Count.Prepare.output a).stacks i=a.stacks i := by
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hi
  · exact Count.Prepare.output_frame a 320
      (Count.Prepare.ports_gap 320 (by norm_num) (by norm_num)) (by norm_num)
  · exact Count.Prepare.output_frame a 322
      (Count.Prepare.ports_gap 322 (by norm_num) (by norm_num)) (by norm_num)
  · exact False.elim (ho rfl)
  all_goals apply Count.Prepare.output_high_frame
  all_goals try omega

theorem samples_prepared_register (a : Data) (i : Fin 40) (hi : 2 ≤ i.val) :
    (Samples.prepared a).regs i=a.regs i := by
  have hn0 : i≠0 := by intro h; subst i; norm_num at hi
  have hn1 : i≠1 := by intro h; subst i; norm_num at hi
  simp [Samples.prepared,LeafAssignmentSetupProgram.cleared,readRegs,hn0,hn1]

theorem finished_register (a : Data) (i : Fin 40) (hi : 2 ≤ i.val) :
    (Residual.finished a).regs i=a.regs i := by
  have hn0 : i≠0 := by intro h; subst i; norm_num at hi
  have hn1 : i≠1 := by intro h; subst i; norm_num at hi
  simp [Residual.finished,LeafAssignmentSetupProgram.cleared,readRegs,hn0,hn1]

theorem finished_protected (a : Data) (i : Fin 768) (hi : Query.Protected i) :
    (Residual.finished a).stacks i=a.stacks i := by
  apply Residual.finished_frame
  all_goals intro h; subst i; norm_num [Query.Protected,Fin.ext_iff] at hi

theorem samples_prepared_protected (a : Data) (i : Fin 768) (hi : Query.Protected i) :
    (Samples.prepared a).stacks i=a.stacks i := by
  apply Samples.prepared_frame
  all_goals intro h; subst i; norm_num [Query.Protected,Fin.ext_iff] at hi

theorem protectedWork_of_frame (base a b : Data)
    (ha : Query.ProtectedWork base (Marked.Wide.workspace a))
    (hf : ∀ i,Query.Protected i → i≠323 → b.stacks i=a.stacks i) :
    Query.ProtectedWork base (Marked.Wide.workspace b) := by
  intro i hi
  change b.stacks (Marked.Wide.workPort i)=_
  rw [hf _ hi (Query.workspace_port_ne i 323 (by decide) (by decide))]
  exact ha i hi

end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
