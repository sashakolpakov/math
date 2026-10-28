import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyScopeBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputEntry

namespace OAI.Algorithms

/-! Native-scope specialization of the fixed weighted packing selector. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SqrtLog.Packing

def raw (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  PackingIncidenceProgram.generatedRawPairs (PackingIncidenceInput.Install.plans scopes n mask)
def pairs (scopes : List (List ℕ)) (mask : List Bool) :=
  (PackingIncidenceInput.Finished.incidenceList scopes mask).product (PackingIncidenceInput.Finished.incidenceList scopes mask)
def terms (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (Q : ℕ) :
    List (ScoreTerm (PackingIncidenceInput.Semantics.Incidences scopes mask) (Fin n) Q) :=
  (pairs scopes mask).map Sum.inl ++ PackingHeadIncremental.headTerms (List.finRange n)

def weights (n s M r q : ℕ) (hs : 0 < s) (hr : 0 < r) (hq : 0 < q) : Weights :=
  Weights.ofFractions M (s*q^2) n (2*r)
    (Nat.mul_pos hs (pow_pos hq 2)) (Nat.mul_pos (by decide) hr)

def values (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
    {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q)) (s : ℕ) (hs : 0 < s) (hr : 0 < r) :=
  selectedValues (PackingIncidenceInput.Semantics.owner scopes n mask hmask) (PackingIncidenceInput.Semantics.factor scopes n mask hmask)
    a tail (terms scopes n mask Q) (PackingIncidenceInput.Semantics.seedIndices n (PackingIncidenceInput.Semantics.factorCount scopes mask))
    (weights n s (PackingIncidenceInput.Semantics.nativeEntries scopes mask).length r (a::tail).length hs hr (by simp))

def rows (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
    {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q)) (s : ℕ) (hs : 0 < s) (hr : 0 < r) :=
  (values scopes n mask hmask a tail s hs hr).reverse.map ReadPlan.encodeWord

def cost (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q)) (s : ℕ)
    (nb sb mb rb : List Bool) : ℕ :=
  controllerCost a tail (pairs scopes mask) (List.finRange n)
    (List.finRange (PackingIncidenceInput.Semantics.factorCount scopes mask)) (raw scopes n mask)
    s (PackingIncidenceInput.Semantics.nativeEntries scopes mask).length nb sb mb rb

def env (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q)) (nb sb mb rb : List Bool) :=
  Assembly.environment (ScoreBuilderRawInput.environment 1 (a::tail)
    (n+PackingIncidenceInput.Semantics.factorCount scopes mask) (raw scopes n mask)) nb sb mb rb

@[simp] theorem rows_length (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hmask : mask.length ≤ n) {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (s : ℕ) (hs : 0 < s) (hr : 0 < r) :
    (rows scopes n mask hmask a tail s hs hr).length=n+PackingIncidenceInput.Semantics.factorCount scopes mask := by
  simp [rows,values,selectedValues,assign_length,PackingIncidenceInput.Semantics.seedIndices,headsFirst_length]

theorem rows_width (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hmask : mask.length ≤ n) {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (s : ℕ) (hs : 0 < s) (hr : 0 < r) :
    ∀ row ∈ rows scopes n mask hmask a tail s hs hr, row.length=Q*r := by
  intro row h
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
  simp [ReadPlan.wordWidth]

theorem rows_bits (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hmask : mask.length ≤ n) {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (s : ℕ) (hs : 0 < s) (hr : 0 < r) :
    (rows scopes n mask hmask a tail s hs hr).flatten.length=
      (n+PackingIncidenceInput.Semantics.factorCount scopes mask)*(Q*r) := by
  have h := rows_length scopes n mask hmask a tail s hs hr
  simp only [rows,List.length_map,List.length_reverse] at h
  rw [rows,encodedWords_length,List.length_reverse,h]
  rfl

theorem generated_pairs (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hmask : mask.length ≤ n) :
    (raw scopes n mask).Perm ((pairs scopes mask).map
      (PackingIncidenceProgram.incidencePair (PackingIncidenceInput.Semantics.owner scopes n mask hmask)
        (PackingIncidenceInput.Semantics.factor scopes n mask hmask) (PackingIncidenceInput.Semantics.seedIndices n (PackingIncidenceInput.Semantics.factorCount scopes mask)))) := by
  exact PackingIncidenceInput.Finished.generated_pairs scopes n mask hmask

theorem run (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
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
      SequentialProgram.Memory ReadPlan.encodeWord a tail 0
        (values scopes n mask hmask a tail s hs (NeZero.pos r)) e.stacks ∧
      e.stacks 11=[] ∧ SequentialProgram.HighState
        (env scopes n mask a tail nb sb mb rb) e.stacks := by
  let owner := PackingIncidenceInput.Semantics.owner scopes n mask hmask
  let factor := PackingIncidenceInput.Semantics.factor scopes n mask hmask
  let indices := PackingIncidenceInput.Semantics.seedIndices n (PackingIncidenceInput.Semantics.factorCount scopes mask)
  let M := (PackingIncidenceInput.Semantics.nativeEntries scopes mask).length
  let evaluator := Assembly.evaluate owner factor (a::tail) (pairs scopes mask) indices a n s M
  let bound := Assembly.scoreBound (a::tail) (pairs scopes mask) indices n s M
  let budget := uniformBudget indices.length (pairs scopes mask).length (raw scopes n mask).length
    (a::tail).length (ReadPlan.wordWidth r Q) n (magnitude n s M r) (parameterBits nb sb mb rb)
  have hil : indices.length=n+PackingIncidenceInput.Semantics.factorCount scopes mask := by
    simp [indices,PackingIncidenceInput.Semantics.seedIndices,headsFirst_length]
  have hb := Assembly.refines owner factor a tail (pairs scopes mask) indices
    (PackingIncidenceInput.Semantics.seedIndices_complete _ _) n s M (raw scopes n mask) nb sb mb rb hn hsb hmb hrb
    (generated_pairs scopes n mask hmask)
  have hbound : ∀ remaining fixed x, remaining+1+fixed.length ≤ indices.length → x∈a::tail →
      evaluator remaining (x::fixed) ≤ bound := by
    intro remaining fixed x hsize _
    exact Assembly.evaluate_bound owner factor (a::tail) (pairs scopes mask) indices a n s M
      remaining fixed x hsize
  obtain ⟨e,htrace,hmem,hcounter,hcontext⟩ := program_memory ReadPlan.encodeWord a tail
    evaluator Assembly.command budget bound indices.length
    (Assembly.environment (ScoreBuilderRawInput.environment 1 (a::tail) indices.length (raw scopes n mask))
      nb sb mb rb) (fun x => by simp) hbound hb d (by simpa only [hil] using hm)
    (by simpa only [hil] using hc) (by simpa [env,hil] using he)
  have horder : ∀ remaining fixed, remaining+1+fixed.length=indices.length → ∀ x y,
      evaluator remaining (x::fixed) ≤ evaluator remaining (y::fixed) ↔
      sequentialNumerator owner factor (a::tail) (terms scopes n mask Q) indices
        (weights n s M r (a::tail).length hs (NeZero.pos r) (by simp)) a remaining (x::fixed) ≤
      sequentialNumerator owner factor (a::tail) (terms scopes n mask Q) indices
        (weights n s M r (a::tail).length hs (NeZero.pos r) (by simp)) a remaining (y::fixed) := by
    intro remaining fixed hsize x y
    simpa [evaluator,Assembly.evaluate,terms,indices,PackingIncidenceInput.Semantics.seedIndices,
      List.length_finRange] using Assembly.candidateScore_order owner factor (a::tail) haN haC (by simp)
      (pairs scopes mask) (List.finRange n) (List.finRange (PackingIncidenceInput.Semantics.factorCount scopes mask))
      (List.nodup_finRange n) (List.mem_finRange)
      (weights n s M r (a::tail).length hs (NeZero.pos r) (by simp)) s M
      (by simp [weights,Weights.ofFractions]) (by rfl) a remaining fixed hsize x y
  have hvalues := assignNat_eq_of_order a tail evaluator
    (sequentialNumerator owner factor (a::tail) (terms scopes n mask Q) indices
      (weights n s M r (a::tail).length hs (NeZero.pos r) (by simp)) a)
    indices.length horder indices.length [] (by simp)
  rw [hvalues] at hmem
  refine ⟨e,?_,hmem,hcounter,?_⟩
  · simpa [cost,controllerCost,budget,bound,indices,M,PackingIncidenceInput.Semantics.seedIndices,List.length_finRange,
      ReadPlan.encodeWord_length] using htrace
  · simpa [env,hil] using hcontext

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
