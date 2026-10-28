import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyScope

namespace OAI.Algorithms

/-! Exact output and preserved high metadata for the native-scope controller. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def Finished (rows : List (List Bool)) (d e : Data) : Prop :=
  e.stacks 8=rows.flatten ∧ e.stacks 11=[] ∧
  e.stacks 9=d.stacks 9 ∧ (e.stacks 10).length=(d.stacks 10).length ∧
  (e.stacks 19).length=rows.length ∧
  (∀ j∈SequentialProgram.scratchPorts, e.stacks j=[]) ∧
  (∀ j : Fin 48,20 ≤ j.val→e.stacks j=d.stacks j)

theorem Finished.length_bound {rows : List (List Bool)} {d e : Data} {B : ℕ}
    (h : Finished rows d e) (hd : ∀ j,(d.stacks j).length ≤ B)
    (hb : rows.flatten.length ≤ B) (hr : rows.length ≤ B) :
    ∀ j,(e.stacks j).length ≤ B := by
  rcases h with ⟨ho,hc,ha,hw,hp,hs,hhi⟩
  intro j
  by_cases hj : 20 ≤ j.val
  · rw [hhi j hj]
    exact hd j
  · have hclass := (show ∀ j : Fin 48,j.val < 20 →
        j∈SequentialProgram.scratchPorts ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=19 by decide) j (by omega)
    rcases hclass with hscratch|rfl|rfl|rfl|rfl|rfl
    · rw [hs j hscratch]; simp
    · simpa only [ho] using hb
    · rw [ha]; exact hd 9
    · rw [hw]; exact hd 10
    · rw [hc]; simp
    · simpa only [hp] using hr

theorem run_output (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
    {r Q : ℕ} [NeZero r] (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (s : ℕ) (hs : 0 < s)
    (nb sb mb rb : List Bool) (hn : SubexponentialSAT.BinaryArithmetic.toNat nb=n)
    (hsb : SubexponentialSAT.BinaryArithmetic.toNat sb=s)
    (hmb : SubexponentialSAT.BinaryArithmetic.toNat mb=(PackingIncidenceInput.Semantics.nativeEntries scopes mask).length)
    (hrb : SubexponentialSAT.BinaryArithmetic.toNat rb=r)
    (d : Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail
      (n+PackingIncidenceInput.Semantics.factorCount scopes mask) [] d.stacks)
    (hc : (d.stacks 11).length=n+PackingIncidenceInput.Semantics.factorCount scopes mask)
    (he : SequentialProgram.HighState (env scopes n mask a tail nb sb mb rb) d.stacks) :
    ∃ e : Data, RunsIn (SequentialProgram.program Assembly.command)
      (cost scopes n mask a tail s nb sb mb rb)
      (d.withPC (some (SequentialProgram.program Assembly.command).entry)) (e.withPC none) ∧
      Finished (rows scopes n mask hmask a tail s hs (NeZero.pos r)) d e := by
  obtain ⟨e,ht,hmem,hc',he'⟩ := run scopes n mask hmask a tail haN haC s hs
    nb sb mb rb hn hsb hmb hrb d hm hc he
  refine ⟨e,ht,?_,hc',hmem.alphabet.trans hm.alphabet.symm,
    hmem.width.trans hm.width.symm,?_,hmem.scratch,?_⟩
  · simpa [rows] using hmem.assignment
  · simpa only [rows,List.length_map,List.length_reverse] using hmem.processed
  · intro j hj
    exact (he' j hj).trans (he j hj).symm

theorem primitive_run (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
    {r Q : ℕ} [NeZero r] (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (s : ℕ) (hs : 0 < s)
    (nb sb mb rb : List Bool) (hn : SubexponentialSAT.BinaryArithmetic.toNat nb=n)
    (hsb : SubexponentialSAT.BinaryArithmetic.toNat sb=s)
    (hmb : SubexponentialSAT.BinaryArithmetic.toNat mb=(PackingIncidenceInput.Semantics.nativeEntries scopes mask).length)
    (hrb : SubexponentialSAT.BinaryArithmetic.toNat rb=r)
    (d : Data)
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail
      (n+PackingIncidenceInput.Semantics.factorCount scopes mask) [] d.stacks)
    (hc : (d.stacks 11).length=n+PackingIncidenceInput.Semantics.factorCount scopes mask)
    (he : SequentialProgram.HighState (env scopes n mask a tail nb sb mb rb) d.stacks) :
    ∃ e : Data, SubexponentialSAT.Computation.RunsIn (primitive (SequentialProgram.program Assembly.command)).step
      (primitiveOverhead (SequentialProgram.program Assembly.command)*cost scopes n mask a tail s nb sb mb rb)
      (primitiveCfg (SequentialProgram.program Assembly.command)
        (d.withPC (some (SequentialProgram.program Assembly.command).entry)))
      (primitiveCfg (SequentialProgram.program Assembly.command) (e.withPC none)) ∧
      Finished (rows scopes n mask hmask a tail s hs (NeZero.pos r)) d e := by
  obtain ⟨e,ht,hf⟩ := run_output scopes n mask hmask a tail haN haC s hs
    nb sb mb rb hn hsb hmb hrb d hm hc he
  exact ⟨e,primitive_execution (SequentialProgram.program Assembly.command) ht,hf⟩

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
