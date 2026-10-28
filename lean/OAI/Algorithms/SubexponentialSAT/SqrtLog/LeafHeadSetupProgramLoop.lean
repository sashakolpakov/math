import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStep

namespace OAI.Algorithms

/-! The actual unary loop visits every head address, in order. Its changing
Cartesian alphabet is formed from the buckets produced by the signed matrix
controller, with an exact list of measured body costs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.UnaryForPrograms
open BucketTupleProgram (HeadTable enumerateFrom)
open BucketTupleProgram.Representative (headsBits tuplesBits)

abbrev headPorts : Ports 16 768 := ⟨648,0,1⟩

def loopMutable : List (Fin 768) := [648,649,650,651,652,660,669,670,671]
def LoopFrame (base a : Data) : Prop :=
  ∀ i, Protected i → i∉loopMutable → a.stacks i=base.stacks i

theorem loopFrame_refl (a : Data) : LoopFrame a a := by intro i hi hn; rfl

theorem loopFrame_popped {base a : Data} (hf : LoopFrame base a) :
    LoopFrame base (popped headPorts a) := by
  intro i hi hn
  have h648 : i≠648 := by intro he; subst i; simp [loopMutable] at hn
  exact (popped_other headPorts a i h648).trans (hf i hi hn)

def ProducedHead (base : Data) (n N D : ℕ) (rows : List (List Bool)) (low : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (B z : ℕ) (table : HeadTable) : Prop :=
  ∃ matrixRows shifted,
    LayoutMatrixProgram.MatrixRel Rel B D (selectedHeads n rows low z) matrixRows ∧
    List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (base.stacks 141))) matrixRows shifted ∧
    table=⟨selectedMask n rows low z, selectedContext n N rows z,
      BucketTupleProgram.actualBuckets (base.stacks 141) shifted (selectedHeads n rows low z)
        n (selectedHeads n rows low z).length⟩

inductive ProducedHeads (base : Data) (n N D : ℕ) (rows : List (List Bool)) (low : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (B : ℕ) : ℕ → List HeadTable → Prop
  | nil (z) : ProducedHeads base n N D rows low Rel B z []
  | cons {z h hs} (head : ProducedHead base n N D rows low Rel B z h)
      (tail : ProducedHeads base n N D rows low Rel B (z+1) hs) :
      ProducedHeads base n N D rows low Rel B z (h::hs)

theorem producedHead_valid {base : Data} {n N D : ℕ} {rows : List (List Bool)}
    {low : List Bool} {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ}
    {table : HeadTable} (hp : ProducedHead base n N D rows low Rel B z table) :
    ∀ b∈table.buckets,BucketTupleProgram.Representative.Valid n
      (⟨table.mask,table.context,b.2⟩ : MomentsAssembly.HeadInput) := by
  obtain ⟨mr,ys,hr,hy,rfl⟩ := hp
  exact BucketTupleProgram.actualBuckets_valid _ _ _ n _
    (HeadIdentifierProgram.chosenIds_bound _ _) _ _
    (HeadScatterProgram.mask_length _ _ _ (HeadIdentifierProgram.chosenIds_bound _ _))

theorem producedHeads_valid {base : Data} {n N D : ℕ} {rows : List (List Bool)}
    {low : List Bool} {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {B z : ℕ}
    {tables : List HeadTable} (hp : ProducedHeads base n N D rows low Rel B z tables) :
    ∀ table∈tables,∀ b∈table.buckets,BucketTupleProgram.Representative.Valid n
      (⟨table.mask,table.context,b.2⟩ : MomentsAssembly.HeadInput) := by
  induction hp with
  | nil => simp
  | cons hh ht ih =>
      intro table htable
      rcases List.mem_cons.mp htable with rfl|htable
      · exact producedHead_valid hh
      · exact ih table htable

/-- A measured observation contains the actual before/after states, local
matrix execution, and the exact normalized endpoint. -/
abbrev CostRecord (entry : Cmd 16 256) (base : Data) (n N D W : ℕ)
    (rows : List (List Bool)) (low : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B z : ℕ)
    (prior : BucketTupleProgram.Representative.Tuples) (table : HeadTable)
    (cost : ℕ) (a e : Data) : Prop :=
  LoopFrame base a ∧ a.stacks 649=unary z ∧ a.stacks 660=tuplesBits prior ∧
  ∃ rp mb rt mr ys,
    LayoutMatrixProgram.MatrixRel Rel B D (selectedHeads n rows low z) mr ∧
    List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (base.stacks 141))) mr ys ∧
    table=⟨selectedMask n rows low z,selectedContext n N rows z,
      BucketTupleProgram.actualBuckets (base.stacks 141) ys (selectedHeads n rows low z)
        n (selectedHeads n rows low z).length⟩ ∧
    Eval (headStep entry) cost a e ∧
    MatrixExecution entry (preparedHead a rp n N rows low W z) D n
      (selectedHeads n rows low z) T B mr ys mb ∧
    e=headStepResult a rp mb rt n N W z rows (prior.map headsBits) low ys ∧
    cost ≤ headStepCost a rp mb rt n N D W z T B rows (prior.map headsBits) low mr ys

inductive CostTrace (entry : Cmd 16 256) (base : Data) (n N D W : ℕ)
    (rows : List (List Bool)) (low : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ) :
    ℕ → BucketTupleProgram.Representative.Tuples → List HeadTable → List ℕ → Data → Data → Prop
  | nil (z : ℕ) (prior : BucketTupleProgram.Representative.Tuples) (a : Data)
      (hc : a.stacks 648=[]) :
      CostTrace entry base n N D W rows low Rel T B z prior [] [] a (popped headPorts a)
  | cons {z : ℕ} {prior : BucketTupleProgram.Representative.Tuples}
      {table : HeadTable} {tables : List HeadTable} {cost : ℕ} {costs : List ℕ} {a e f : Data}
      (hne : a.stacks 648≠[])
      (record : CostRecord entry base n N D W rows low Rel T B z prior table cost (popped headPorts a) e)
      (hc : e.stacks 648=(popped headPorts a).stacks 648)
      (tail : CostTrace entry base n N D W rows low Rel T B (z+1)
        (BucketTupleProgram.extend prior table.choices) tables costs e f) :
      CostTrace entry base n N D W rows low Rel T B z prior (table::tables) (cost::costs) a f

/-- Every callback below is the concrete `headStep`: the only service premise
is the separately verified integer-entry bank contract. -/
theorem headLoop_visits (entry : Cmd 16 256) (base : Data) (n N D W : ℕ)
    (rows : List (List Bool)) (low : List Bool)
    (hn : base.stacks 128=unary n) (hN : base.stacks 129=unary N)
    (hW : base.stacks 132=unary W) (hrows : base.stacks 133=rows.flatten)
    (hlow : base.stacks 134=low) (hD : base.stacks 647=unary D)
    (hmark : base.stacks 665=[false])
    (hw : ∀ row∈rows,row.length=W) (hsize : n+N ≤ rows.length)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ)
    (hc : ∀ a z regs,LoopFrame base a→LayoutMatrixProgram.EntryContract entry
      (matrixBase (preparedHead a regs n N rows low W z)) Valid Rel T B)
    (hv : ∀ z j,j < D→∀ v∈selectedHeads n rows low z,Valid j v)
    (word : List Bool) :
    ∀ a z prior,LoopFrame base a→a.stacks 648=word→a.stacks 649=unary z→
      a.stacks 660=tuplesBits prior→
      ∃ tables costs t e,
        ProducedHeads base n N D rows low Rel B z tables ∧
        tables.length=word.length ∧ Visits headPorts (headStep entry) costs t a e ∧
        e.stacks 660=tuplesBits (enumerateFrom tables prior) ∧
        e.stacks 649=unary (z+word.length) ∧ LoopFrame base e ∧
        CostTrace entry base n N D W rows low Rel T B z prior tables costs a e := by
  induction word with
  | nil =>
      intro a z prior hf hcounter hz hp
      refine ⟨[],[],2,popped headPorts a,.nil z,rfl,.done a hcounter,?_,?_,loopFrame_popped hf,.nil z prior a hcounter⟩
      · simpa [enumerateFrom] using (popped_other headPorts a 660 (by decide)).trans hp
      · simpa using (popped_other headPorts a 649 (by decide)).trans hz
  | cons bit word ih =>
      intro a z prior hf hcounter hz hp
      let p := popped headPorts a
      have pf : LoopFrame base p := loopFrame_popped hf
      have source (i : Fin 768) (hi : Protected i) (hne : i∉loopMutable) :
          p.stacks i=base.stacks i := pf i hi hne
      have pz : p.stacks 649=unary z := (popped_other headPorts a 649 (by decide)).trans hz
      have pp : p.stacks 660=ProgramEncoding.encodeRecords (prior.map headsBits) := by
        rw [←BucketTupleProgram.tuplesBits_eq]
        exact (popped_other headPorts a 660 (by decide)).trans hp
      obtain ⟨mr,ys,nb,e,hr,hy,he,hep,hez,hecounter,heclean,heframe,hstepcost⟩ :=
        headStep_eval entry p n N D W z rows (prior.map headsBits) low
          ((source 128 (by decide) (by simp [loopMutable])).trans hn)
          ((source 129 (by decide) (by simp [loopMutable])).trans hN)
          ((source 132 (by decide) (by simp [loopMutable])).trans hW)
          ((source 133 (by decide) (by simp [loopMutable])).trans hrows)
          ((source 134 (by decide) (by simp [loopMutable])).trans hlow)
          ((source 647 (by decide) (by simp [loopMutable])).trans hD) pz pp
          ((source 665 (by decide) (by simp [loopMutable])).trans hmark) hw hsize
          Valid Rel T B (fun regs=>hc p z regs pf) (hv z)
      have p141 : p.stacks 141=base.stacks 141 := source 141 (by decide) (by simp [loopMutable])
      rw [p141] at hy hep
      let table : HeadTable := ⟨selectedMask n rows low z,selectedContext n N rows z,
        BucketTupleProgram.actualBuckets (base.stacks 141) ys (selectedHeads n rows low z)
          n (selectedHeads n rows low z).length⟩
      have htable : ProducedHead base n N D rows low Rel B z table := ⟨mr,ys,hr,hy,rfl⟩
      have ep : e.stacks 660=tuplesBits (BucketTupleProgram.extend prior table.choices) := by
        rw [BucketTupleProgram.tuplesBits_eq]
        rw [←BucketTupleProgram.nextRows_eq]
        exact hep
      have ef : LoopFrame base e := by
        intro i hi hne
        have hn' : i∉([649,650,651,652,660,669,670,671] : List (Fin 768)) := by
          intro hm
          apply hne
          exact List.mem_cons_of_mem 648 hm
        exact (heframe i hi hn').trans (pf i hi hne)
      have ecounter : e.stacks 648=word := by
        rw [hecounter]
        change (a.stacks 648).tail=word
        rw [hcounter]
        rfl
      obtain ⟨tables,costs,nt,f,htables,hlen,ht,hfp,hfz,hff,htrace⟩ :=
        ih e (z+1) (BucketTupleProgram.extend prior table.choices) ef ecounter hez ep
      refine ⟨table::tables,nb::costs,nb+nt+2,f,.cons htable htables,?_,
        .step (by simp [hcounter]) he hecounter ht,?_,?_,hff,?_⟩
      · simpa using congrArg Nat.succ hlen
      · exact hfp
      · simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hfz
      · apply CostTrace.cons (by simp [hcounter]) _ hecounter htrace
        obtain ⟨rp,mb,rt,hmatrix,hresult,hcost⟩ := hstepcost
        refine ⟨pf,pz,?_,rp,mb,rt,mr,ys,hr,hy,rfl,he,hmatrix,hresult,hcost⟩
        exact (popped_other headPorts a 660 (by decide)).trans hp

theorem headLoop_measured (entry : Cmd 16 256) (base : Data) (n N D W : ℕ)
    (rows : List (List Bool)) (low : List Bool)
    (hn : base.stacks 128=unary n) (hN : base.stacks 129=unary N)
    (hW : base.stacks 132=unary W) (hrows : base.stacks 133=rows.flatten)
    (hlow : base.stacks 134=low) (hD : base.stacks 647=unary D)
    (hmark : base.stacks 665=[false])
    (hw : ∀ row∈rows,row.length=W) (hsize : n+N ≤ rows.length)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ)
    (hc : ∀ a z regs,LoopFrame base a→LayoutMatrixProgram.EntryContract entry
      (matrixBase (preparedHead a regs n N rows low W z)) Valid Rel T B)
    (hv : ∀ z j,j < D→∀ v∈selectedHeads n rows low z,Valid j v)
    (a : Data) (z : ℕ) (prior : BucketTupleProgram.Representative.Tuples)
    (hf : LoopFrame base a) (hz : a.stacks 649=unary z) (hp : a.stacks 660=tuplesBits prior) :
    ∃ tables costs t e,
      ProducedHeads base n N D rows low Rel B z tables ∧
      tables.length=(a.stacks 648).length ∧ costs.length=tables.length ∧
      Eval (headLoop entry) t a e ∧ t=costs.sum+2*tables.length+2 ∧
      e.stacks 648=[] ∧ e.stacks 660=tuplesBits (enumerateFrom tables prior) ∧
      e.stacks 649=unary (z+tables.length) ∧ LoopFrame base e ∧
      CostTrace entry base n N D W rows low Rel T B z prior tables costs a e := by
  obtain ⟨tables,costs,t,e,ht,hlen,hvis,hp',hz',hf',htrace⟩ :=
    headLoop_visits entry base n N D W rows low hn hN hW hrows hlow hD hmark hw hsize
      Valid Rel T B hc hv (a.stacks 648) a z prior hf rfl hz hp
  obtain ⟨hcostlen,hend,htime⟩ := hvis.bounds
  refine ⟨tables,costs,t,e,ht,hlen,?_,hvis.eval,?_,hend,hp',?_,hf',htrace⟩
  · exact hcostlen.trans hlen.symm
  · simpa only [hcostlen,hlen] using htime
  · simpa only [hlen] using hz'

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
