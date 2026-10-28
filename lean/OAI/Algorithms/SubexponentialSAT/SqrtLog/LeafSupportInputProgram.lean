import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafSupportInputProgramLocal

namespace OAI.Algorithms

/-! The native support-list producer preserves its source metadata and writes
only the reusable raw-frame support master. All private work is restored. -/
namespace SubexponentialSAT.SqrtLog.LeafSupportInputProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.MomentsAssembly (rawFrames)

abbrev Data := State 40 768
abbrev Code := Cmd 40 768
abbrev registers : Fin 10 → Fin 40 := Fin.castAdd 30
def ports : Fin 13 → Fin 768 := ![340,341,342,343,344,345,346,347,348,349,128,243,169]
def privatePorts : Fin 10 → Fin 768 := ![340,341,342,343,344,345,346,347,348,349]
theorem ports_injective : Function.Injective ports := by decide

def Ready (d : Data) : Prop := d.stacks 169=[] ∧ ∀i, d.stacks (privatePorts i)=[]
def command : Code := .call (ProgramLinking.liftProgram Local.program registers ports)
def program := compiled command 128 169
def cost (n J : ℕ) : ℕ := Local.cost n J+1

theorem supportFrames_length {n : ℕ} (ss : List (Finset (Fin n))) :
    (rawFrames (ss.map Squarefree.encodeMask)).length = ss.length*(2*n+1) := by
  induction ss with
  | nil => simp []
  | cons s ss ih =>
      simp only [List.map_cons,rawFrames,List.length_append,Encoding.length_frame,
        Squarefree.encodeMask_length,List.length_cons,ih]
      ring

theorem program_runsIn (d : Data) (hd : Ready d) :
    ∃ (b : Data) (ss : List (Finset (Fin (d.stacks 128).length))),
      ss.Nodup ∧ (∀s, s∈ss ↔ s.card < (d.stacks 243).length) ∧
      ss.length=SupportProgram.count (d.stacks 128).length (d.stacks 243).length ∧
      b.stacks 169=rawFrames (ss.map Squarefree.encodeMask) ∧
      (∀i, i≠169 → b.stacks i=d.stacks i) ∧
      (∀ (i : Fin 40), Nat.le 10 (Fin.val i) → b.regs i = d.regs i) ∧
      RunsIn program (cost (d.stacks 128).length (d.stacks 243).length)
        (d.withPC (some program.entry)) (b.withPC none) := by
  obtain ⟨rf,rows,hrows,t,ht,he⟩ := Local.program_runsIn (d.regs ∘ registers)
    (d.stacks 128) (d.stacks 243)
  have hp : projectState registers ports d =
      Local.initial (d.regs ∘ registers) (d.stacks 128) (d.stacks 243) := by
    rcases hd with ⟨ho,hp⟩
    simp only [Fin.forall_fin_succ] at hp
    apply congrArg (StructuredProgram.State.mk (d.regs ∘ registers))
    funext i; fin_cases i <;>
      simp_all [ports,privatePorts,Local.initial,Local.state]
  rw [←hp] at he
  have hc := eval_call_from_state Local.program registers ports d
    (Fin.castAdd_injective _ _) ports_injective he
  let out := Local.final rf (d.stacks 128) (d.stacks 243) (rawFrames rows.reverse)
  let b := embedState registers ports d out
  let ss := (SupportProgram.supports (d.stacks 128).length rows).reverse
  have henc : ss.map Squarefree.encodeMask=rows.reverse := by
    simp only [ss,List.map_reverse,SupportProgram.supports_encode _ _ _ hrows]
  refine ⟨b,ss,?_,?_,?_,?_,?_,?_,?_⟩
  · exact List.nodup_reverse.mpr (SupportProgram.supports_nodup _ _ _ hrows)
  · intro s
    simpa [ss] using SupportProgram.mem_supports _ _ _ hrows s
  · simpa [ss] using SupportProgram.supports_length _ _ _ hrows
  · rw [henc]
    have h := embedState_stack registers ports d out ports_injective (12 : Fin 13)
    simpa [b,ports,out,Local.final,Local.state] using h
  · intro i hi
    by_cases him : ∃j, ports j=i
    · obtain ⟨j,rfl⟩ := him
      rw [show b.stacks (ports j)=out.stacks j from
        embedState_stack registers ports d out ports_injective j]
      rcases hd with ⟨ho,hp⟩
      simp only [Fin.forall_fin_succ] at hp
      fin_cases j <;> simp_all [privatePorts,ports,out,Local.final,Local.state]
    · exact embedState_stack_frame registers ports d out i him
  · intro i hi
    apply embedState_register_frame registers ports d out i
    rintro ⟨j,hj⟩
    have hsmall : i.val < 10 := by
      rw [←hj]
      exact j.isLt
    exact (Nat.not_lt_of_ge hi) hsmall
  · change Eval command t d b at hc
    exact ⟨t+1,by dsimp [cost]; omega,compiled_halt_trace hc 128 169⟩

/-- Native cost still uses the exact binomial support count. No ambient
powerset or n^J candidate search is hidden in this bound. -/
theorem cost_bound (n J : ℕ) (hJ : 0 < J) :
    cost n J ≤ 5000*(n+1)*(n+J+1)*(SupportProgram.count n J+1) := by
  let A := (n+1)*(n+J+1)
  let M := SupportProgram.count n J
  have hg := SupportProgram.total_cost_le n J hJ
  have hAn : n+1 ≤ A := by dsimp [A]; nlinarith
  have hAJ : J+1 ≤ A := by dsimp [A]; nlinarith
  have hA : 1 ≤ A := by omega
  have hterm : M*(11*n+13) ≤ 13*A*M := by
    calc
      _ ≤ M*(13*A) := Nat.mul_le_mul_left M (by omega)
      _ = _ := by ring
  have htail : 7*n+9*J+45 ≤ 61*A := by omega
  change 7*n+9*J+SupportProgram.Loop.cost n J+M*(11*n+13)+74 ≤ _
  have hg' : SupportProgram.Loop.cost n J+29 ≤ 4000*A*M := by
    simpa [A,M,Nat.mul_assoc] using hg
  calc
    _ ≤ 5000*A*(M+1) := by nlinarith
    _ = _ := by dsimp [A,M]; ring

theorem program_primitive (d : Data) (hd : Ready d) (hJ : 0 < (d.stacks 243).length) :
    ∃ (b : Data) (ss : List (Finset (Fin (d.stacks 128).length))),
      ss.Nodup ∧ (∀s, s∈ss ↔ s.card < (d.stacks 243).length) ∧
      ss.length=SupportProgram.count (d.stacks 128).length (d.stacks 243).length ∧
      b.stacks 169=rawFrames (ss.map Squarefree.encodeMask) ∧
      (∀i, i≠169 → b.stacks i=d.stacks i) ∧
      (∀ (i : Fin 40), Nat.le 10 (Fin.val i) → b.regs i = d.regs i) ∧
      SubexponentialSAT.Computation.RunsIn (primitive program).step
        (primitiveOverhead program *
          (5000*((d.stacks 128).length+1)*((d.stacks 128).length+(d.stacks 243).length+1)*
            (SupportProgram.count (d.stacks 128).length (d.stacks 243).length+1)))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (b.withPC none)) := by
  obtain ⟨b,ss,hn,hm,hl,ho,hf,hr,t,ht,he⟩ := program_runsIn d hd
  have hb := cost_bound (d.stacks 128).length (d.stacks 243).length hJ
  have hrun : RunsIn program
      (5000*((d.stacks 128).length+1)*((d.stacks 128).length+(d.stacks 243).length+1)*
        (SupportProgram.count (d.stacks 128).length (d.stacks 243).length+1))
      (d.withPC (some program.entry)) (b.withPC none) := ⟨t,ht.trans hb,he⟩
  exact ⟨b,ss,hn,hm,hl,ho,hf,hr,primitive_execution program hrun⟩

end SubexponentialSAT.SqrtLog.LeafSupportInputProgram

end OAI.Algorithms
