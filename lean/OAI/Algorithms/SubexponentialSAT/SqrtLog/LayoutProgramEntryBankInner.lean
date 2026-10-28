import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankFramePrepare

namespace OAI.Algorithms

/-! The actual cached universal-entry call, including all physical staging,
export and cleanup. The caller's private fiber-loop bank is unrestricted. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open RowSelectionProgram

variable {r Q : ℕ}

structure Cached (a : Data) (c : Numerator.Saved) (t : Fin Q)
    (u y : UniversalType r Q 1) : Prop where
  low : ∀ j : Fin 256, j.val < 64 → a.stacks j=[]
  temp : a.stacks 199=[]
  posEmpty : a.stacks 254=[]
  negEmpty : a.stacks 255=[]
  hp : a.stacks 202=c.hp
  hn : a.stacks 203=c.hn
  hw : a.stacks 204=c.width
  hpos : a.stacks 205=c.power.1
  hneg : c.power.2=[]
  hr : a.stacks 206=c.r
  ha : a.stacks 207=c.a
  colors : a.stacks 208=List.replicate r true
  nodes : a.stacks 209=List.replicate Q true
  node : a.stacks 210=List.replicate t.val true
  typeWidth : a.stacks 211=List.replicate (Q*r) true
  rowType : a.stacks 65=CollisionProgram.encodeType u
  colType : a.stacks 68=CollisionProgram.encodeType y

def finish (a : Data) (regs : Fin 16 → Bool) (result : WordPair) : Data :=
  ⟨regs,fun j => if j.val < 200 then [] else if j=255 then result.2
    else if j=254 then result.1 else a.stacks j⟩

def inner : Code := .seq prepare (.seq integer (.seq exportPair cleanup))

private theorem prepareSize_le (a : Data) (S : ℕ)
    (h : ∀ j : Fin 256, j.val < 212 → (a.stacks j).length ≤ S) :
    prepareSize a ≤ 12*S := by
  have h1 := h 202 (by decide)
  have h2 := h 203 (by decide)
  have h3 := h 204 (by decide)
  have h4 := h 205 (by decide)
  have h5 := h 206 (by decide)
  have h6 := h 207 (by decide)
  have h7 := h 208 (by decide)
  have h8 := h 209 (by decide)
  have h9 := h 210 (by decide)
  have h10 := h 211 (by decide)
  have h11 := h 65 (by decide)
  have h12 := h 68 (by decide)
  unfold prepareSize
  omega

private theorem update_length_le (f : Fin 256 → List Bool) (i j : Fin 256)
    (v : List Bool) (B : ℕ) (hf : (f j).length ≤ B) (hv : v.length ≤ B) :
    (Function.update f i v j).length ≤ B := by
  by_cases h : j=i
  · subst j; simpa using hv
  · simpa [Function.update_of_ne h] using hf

private theorem prepared_length (a : Data) (S : ℕ)
    (hl : ∀ j : Fin 256, j.val < 64 → a.stacks j=[])
    (h : ∀ j : Fin 256, j.val < 212 → (a.stacks j).length ≤ S)
    (j : Fin 256) (hj : j.val < 200) :
    ((Staging.result 0 1 prepareOps a).stacks j).length ≤ S+1 := by
  rw [prepare_stacks a hl]
  unfold preparedStacks
  repeat' apply update_length_le
  all_goals first
    | (exact (h _ (by omega)).trans (Nat.le_succ S))
    | (simp only [List.length_singleton]; omega)

/-- This theorem has no value-producing callback: it calls the fixed
`IntegerEntry.command`, and charges staging, export and complete cleanup. -/
theorem inner_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1)
    (a : Data) (S : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : Cached a (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t u y)
    (hsize : ∀ j : Fin 256, j.val < 212 → (a.stacks j).length ≤ S) :
    let L := IntegerEntry.lengthBound R width.length (pairLength power) u y+power.1.length+1
    ∃ n ≤ IntegerEntry.budget aWord.length R width.length (pairLength power) power.1.length t u y+
        484*S+407*L+1073,
      ∃ rf result, Eval inner n a (finish a rf result) ∧
        pairValue result=IntegerEntry.value aWord.length R t u y ∧
        LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧ pairLength result ≤ L := by
  intro L
  let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord
  let p := Staging.result 0 1 prepareOps a
  have hproj := prepare_project a c t u y hc.low hc.hp hc.hn hc.hw hc.hpos hc.hneg hc.hr hc.ha
    hc.colors hc.nodes hc.node hc.typeWidth hc.rowType hc.colType
  obtain ⟨ni,hni,ri,result,hi,hvalue,hmass,hlength⟩ := IntegerEntry.command_eval Hwords width power
    (p.regs ∘ integerRegs) aWord R t u y hlen hwords hvalues hp hpt hpos hwidth hAQ hQ
  let b := IntegerEntry.output c ri t u y result
  have hi' : Eval IntegerEntry.command ni (projectState integerRegs integerPorts p) b := by
    rw [hproj]
    exact hi
  let q := embedState integerRegs integerPorts p b
  let e := Staging.result 0 1 exportOps q
  let z := Staging.result 0 1 cleanupOps e
  obtain ⟨hrun,hout⟩ := prepared_integer_export_cleanup a hc.temp hc.posEmpty hc.negEmpty hi'
  have hbstacks : b.stacks=Function.update (Function.update
      (projectState integerRegs integerPorts p).stacks 53 result.1) 54 result.2 := by
    rw [hproj]
    rfl
  have hqstacks : q.stacks=Function.update (Function.update p.stacks 53 result.1) 54 result.2 := by
    change Function.extend integerPorts b.stacks p.stacks=_
    rw [hbstacks,ProgramLinking.extend_update integerPorts_inj,
      ProgramLinking.extend_update integerPorts_inj]
    have hext := congrArg StructuredProgram.State.stacks
      (embedState_project integerRegs integerPorts p integerRegs_inj integerPorts_inj)
    change Function.update (Function.update
      (embedState integerRegs integerPorts p (projectState integerRegs integerPorts p)).stacks
        (53 : Fin 256) result.1) (54 : Fin 256) result.2 = _
    rw [hext]
  have hz : z=finish a z.regs result := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext j
      calc
        z.stacks j = if j.val < 200 then [] else if j=255 then b.stacks 54
            else if j=254 then b.stacks 53 else a.stacks j := hout j
        _ = (finish a z.regs result).stacks j := by simp [b,IntegerEntry.output,finish]
  have hpl : ∀ j : Fin 256, j.val < 200 → (p.stacks j).length ≤ S+1 :=
    prepared_length a S hc.low hsize
  have hql : ∀ j : Fin 256, j.val < 200 → (q.stacks j).length ≤ S+L+1 := by
    intro j hj
    rw [hqstacks]
    by_cases h54 : j=54
    · subst j
      simp only [Function.update_self]
      change result.1.length+result.2.length ≤ L at hlength
      omega
    · by_cases h53 : j=53
      · subst j
        simp only [Function.update_of_ne (by decide : (53:Fin 256)≠54),Function.update_self]
        change result.1.length+result.2.length ≤ L at hlength
        omega
      · rw [Function.update_of_ne h54,Function.update_of_ne h53]
        have hh := hpl j hj
        omega
  have hq254 : q.stacks 254=[] := by
    rw [hqstacks]
    simpa using (prepare_frame a 254 (by decide)).trans hc.posEmpty
  have hq255 : q.stacks 255=[] := by
    rw [hqstacks]
    simpa using (prepare_frame a 255 (by decide)).trans hc.negEmpty
  have hel : ∀ j : Fin 256, j.val < 200 → (e.stacks j).length ≤ S+L+1 := by
    intro j hj
    change ((Staging.result 0 1 exportOps q).stacks j).length ≤ _
    rw [exportPair_stacks q hq254 hq255]
    have hn254 : j≠254 := by intro h; subst j; omega
    have hn255 : j≠255 := by intro h; subst j; omega
    simpa [hn254,hn255] using hql j hj
  have hcleanup := cleanup_cost_le e (S+L+1) hel
  have hprepare := prepareSize_le a S hsize
  have hexport : Staging.cost 0 1 exportOps q ≤ 7*L+10 := by
    rw [exportPair_cost,hqstacks]
    simp only [Function.update_self,Function.update_of_ne (by decide : (53:Fin 256)≠54)]
    change result.1.length+result.2.length ≤ L at hlength
    omega
  refine ⟨Staging.cost 0 1 prepareOps a+((ni+1)+
      (Staging.cost 0 1 exportOps q+Staging.cost 0 1 cleanupOps e)),?_,z.regs,result,?_,hvalue,hmass,hlength⟩
  · rw [prepare_cost]
    omega
  · change Eval inner _ a z at hrun
    rw [hz] at hrun
    exact hrun

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
