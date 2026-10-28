import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgramInit

namespace OAI.Algorithms

/-! A complete fixed primitive support-mask generator. Only two unary input
stacks are preloaded; the constant alphabet and seed record are written by the
program. Each stage prunes overweight masks before the next expansion. -/
namespace SubexponentialSAT.SqrtLog.SupportProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls Steps

abbrev command : Cmd 10 10 := .seq Init.command Loop.command
def program := compiled command 8 0

theorem program_runsIn (budget : List Bool) (a : Data) (ha : Init.Empty budget a) :
    ∃ (b : Data) (rows : Records), Correct (a.stacks 8).length budget.length rows ∧
      b.stacks 0 = SubexponentialSAT.ProgramEncoding.encodeRecords rows ∧ b.stacks 9 = budget ∧
      RunsIn program (Loop.cost (a.stacks 8).length budget.length + 29)
        (a.withPC (some program.entry)) (b.withPC none) := by
  obtain ⟨i,hi,c,hinit,hc,hdepth⟩ := Init.command_eval budget a ha
  obtain ⟨j,b,hj,hb,hend,hloop⟩ := Loop.command_eval budget c hc
  rcases hb with ⟨rows,hcorrect,h0,h1,h2,h3,h4,h5,h6,h7,h9⟩
  rw [hdepth] at hj hcorrect
  exact ⟨b,rows,hcorrect,h0,h9,i+j+1,by omega,
    compiled_halt_trace (hinit.seq hloop) 8 0⟩

/-- Both runtime integers use unary stacks here; their bits are immaterial.
Every other stack starts empty, including the output. -/
def inputState (depth budget : List Bool) : Data :=
  ⟨fun _ => false, fun i => if i = 8 then depth else if i = 9 then budget else []⟩

theorem initial_runsIn (depth budget : List Bool) :
    ∃ (b : Data) (rows : Records), Correct depth.length budget.length rows ∧
      b.stacks 0 = SubexponentialSAT.ProgramEncoding.encodeRecords rows ∧ b.stacks 9 = budget ∧
      RunsIn program (Loop.cost depth.length budget.length + 29)
        ((inputState depth budget).withPC (some program.entry)) (b.withPC none) := by
  have hi : Init.Empty budget (inputState depth budget) := by
    constructor
    · intro i hi8 hi9; simp [inputState,hi8,hi9]
    · simp [inputState]
  simpa [inputState] using
    program_runsIn budget (inputState depth budget) hi

theorem total_cost_le (n J : ℕ) (hJ : 0 < J) :
    Loop.cost n J + 29 ≤ 4000 * (n+1) * (n+J+1) * count n J := by
  have hb := Loop.cost_le n J hJ
  have hm : 1 ≤ count n J := by
    have hp : (List.replicate n false) ∈ masks n J := by simp [List.count_replicate,hJ]
    have hh : 0 < (masks n J).length := List.length_pos_iff.mpr (by
      intro h
      rw [h] at hp
      exact (List.not_mem_nil hp).elim)
    rw [masks_length] at hh
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hh)
  have hone : 1 ≤ (n+1)*(n+J+1)*count n J := by
    have h1 := Nat.mul_le_mul (show 1 ≤ n+1 by omega) (show 1 ≤ n+J+1 by omega)
    have h2 := Nat.mul_le_mul h1 hm
    simpa using h2
  nlinarith

/-- Executed output enumerates each squarefree support exactly once, with a
bound polynomial in n,J times the exact binomial count M_J. -/
theorem primitive_runsIn (depth budget : List Bool) (hJ : 0 < budget.length) :
    ∃ (b : Data) (rows : Records), Correct depth.length budget.length rows ∧
      b.stacks 0 = SubexponentialSAT.ProgramEncoding.encodeRecords rows ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program *
          (4000 * (depth.length+1) * (depth.length+budget.length+1) * count depth.length budget.length))
        (primitiveCfg program ((inputState depth budget).withPC (some program.entry)))
        (primitiveCfg program (b.withPC none)) := by
  obtain ⟨b,rows,hcorrect,hout,hbudget,htrace⟩ := initial_runsIn depth budget
  have hp := primitive_execution program htrace
  obtain ⟨t,ht,hp⟩ := hp
  exact ⟨b,rows,hcorrect,hout,t,
    ht.trans (Nat.mul_le_mul_left _ (total_cost_le depth.length budget.length hJ)),hp⟩

end SubexponentialSAT.SqrtLog.SupportProgram

end OAI.Algorithms
