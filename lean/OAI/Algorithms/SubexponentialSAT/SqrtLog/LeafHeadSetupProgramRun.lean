import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramInitialize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramLoop

namespace OAI.Algorithms

/-! Measured execution of the complete per-node setup, conditional only on
its explicit concrete integer-entry service. Uniform numerical resource bounds
are proved separately. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open BucketTupleProgram (enumerate)

abbrev CacheCorrect (height R width : List Bool) (words : List (List Bool)) : Prop :=
  words.length=R.length ∧ (∀ w∈words,w.length=width.length) ∧
    words.map SubexponentialSAT.BinaryArithmetic.toNat=
      (List.range R.length).map (LayoutCoefficientRecurrence.H height.length)

abbrev NodeEntry (entry : Cmd 16 256) (a : Data) (n N W r t : ℕ)
    (records rows : List (List Bool)) (low height R width : List Bool)
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ) : Prop :=
  ∀ ra rd rc words,CacheCorrect height R width words→∀ b z regs,
    LoopFrame (nodeStart a ra rd rc r t records height R width words) b→
    LayoutMatrixProgram.EntryContract entry (matrixBase (preparedHead b regs n N rows low W z))
      Valid Rel T B

abbrev External (i : Fin 768) : Prop :=
  (i.val < 340 ∨ (628 ≤ i.val ∧ i.val < 640) ∨ 680 ≤ i.val) ∧
    i≠163 ∧ i≠710 ∧ i≠711 ∧ i≠712

theorem external_protected {i : Fin 768} (h : External i) : Protected i := by
  constructor
  · omega
  · intro he
    have hh := congrArg Fin.val he
    simp [temporary] at hh
    omega

theorem external_ne_private {i : Fin 768} (h : External i) (j : Fin 768)
    (hj : 640 ≤ j.val ∧ j.val < 680) : i≠j := by
  intro he
  have hh := congrArg Fin.val he
  omega

theorem external_not_start {i : Fin 768} (h : External i) :
    i∉([640,641,642,643,647,648,649,660,665,710,711,712] : List (Fin 768)) := by
  have hp := external_ne_private h
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨hp 640 (by decide),hp 641 (by decide),hp 642 (by decide),hp 643 (by decide),
    hp 647 (by decide),hp 648 (by decide),hp 649 (by decide),hp 660 (by decide),
    hp 665 (by decide),h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩

theorem external_not_loop {i : Fin 768} (h : External i) : i∉loopMutable := by
  have hp := external_ne_private h
  simp only [loopMutable,List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨hp 648 (by decide),hp 649 (by decide),hp 650 (by decide),hp 651 (by decide),
    hp 652 (by decide),hp 660 (by decide),hp 669 (by decide),hp 670 (by decide),hp 671 (by decide)⟩


def nodeCost (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (n r node : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (tables : List BucketTupleProgram.HeadTable) (costs : List ℕ) (loopEnd : Data)
    (rf : Fin 8 → Bool) : ℕ :=
  initializeCost a ra rd rc r node records height R width words+
    (costs.sum+2*tables.length+2)+
    finalCost loopEnd rf (unary n) (enumerate tables)+
    clearManyCost cleanupPorts (finalResult loopEnd rf (unary n) (enumerate tables))

theorem command_eval (entry : Cmd 16 256) (a : Data) (n N W r node : ℕ)
    (records rows : List (List Bool)) (low height R width : List Bool)
    (hn : a.stacks 128=unary n) (hN : a.stacks 129=unary N)
    (hr : a.stacks 130=unary r) (hnode : a.stacks 307=unary node)
    (hW : a.stacks 132=unary W) (hrows : a.stacks 133=rows.flatten)
    (hlow : a.stacks 134=low) (hrecords : a.stacks 136=Encoding.encodeList id records)
    (hheight : a.stacks 139=height) (hR : a.stacks 138=R) (hwidth : a.stacks 140=width)
    (hw : ∀ row∈rows,row.length=W) (hsize : n+N ≤ rows.length)
    (hwidthBound : 1+2*height.length*R.length ≤ width.length)
    (h660 : a.stacks 660=[]) (h665 : a.stacks 665=[])
    (Valid : ℕ → ℕ → Prop) (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B : ℕ)
    (hc : NodeEntry entry a n N W r node records rows low height R width Valid Rel T B)
    (hv : ∀ z j,j < records.length→∀ v∈selectedHeads n rows low z,Valid j v) :
    ∃ ra rd rc words tables costs steps e,
      CacheCorrect height R width words ∧
      ProducedHeads (nodeStart a ra rd rc r node records height R width words)
        n N records.length rows low Rel B (node*r) tables ∧
      tables.length=r ∧ costs.length=r ∧ Eval (command entry) steps a e ∧
      e.stacks 163=MomentsAssembly.bucketsInput
        (((enumerate tables).map (BucketTupleProgram.Representative.bucket n)).reverse) ∧
      (∀ i,External i→e.stacks i=a.stacks i) ∧
      (∀ i : Fin 768,640 ≤ i.val ∧ i.val < 680→e.stacks i=[]) ∧
      (∀ i : Fin 288,e.stacks (workPort (by decide) i)=[]) ∧
      e.stacks 710=words.flatten++a.stacks 710 ∧
      e.stacks 711=List.replicate (R.length*width.length) false++a.stacks 711 ∧
      e.stacks 712=LayoutProgram.IntegerCache.denominatorWord R.length++a.stacks 712 ∧
      (∃ loopEnd rf,
        CostTrace entry (nodeStart a ra rd rc r node records height R width words)
          n N records.length W rows low Rel T B (node*r) [[]] tables costs
          (nodeStart a ra rd rc r node records height R width words) loopEnd ∧
        e=clearManyState cleanupPorts (finalResult loopEnd rf (unary n) (enumerate tables)) ∧
        steps ≤ nodeCost a ra rd rc n r node records height R width words tables costs loopEnd rf ∧
        loopEnd.stacks 660=BucketTupleProgram.Representative.tuplesBits (enumerate tables) ∧
        loopEnd.stacks 128=unary n) := by
  obtain ⟨ra,rd,rc,words,ti,hti,hei,hlen,hwords,hvalues⟩ := initialize_eval a r node records
    height R width hr hnode hrecords hheight hR hwidth hwidthBound
  let b := nodeStart a ra rd rc r node records height R width words
  have hcache : CacheCorrect height R width words := ⟨hlen,hwords,hvalues⟩
  have bf (i : Fin 768) (hi : Protected i)
      (hne : i∉([640,641,642,643,647,648,649,660,665,710,711,712] : List (Fin 768))) :
      b.stacks i=a.stacks i := nodeStart_frame a ra rd rc r node records height R width words i hi hne
  have bn : b.stacks 128=unary n := (bf 128 (by decide) (by simp)).trans hn
  have bN : b.stacks 129=unary N := (bf 129 (by decide) (by simp)).trans hN
  have bW : b.stacks 132=unary W := (bf 132 (by decide) (by simp)).trans hW
  have brows : b.stacks 133=rows.flatten := (bf 133 (by decide) (by simp)).trans hrows
  have blow : b.stacks 134=low := (bf 134 (by decide) (by simp)).trans hlow
  have bD : b.stacks 647=unary records.length := nodeStart_dimension a ra rd rc r node records height R width words
  have bm : b.stacks 665=[false] := nodeStart_marker a ra rd rc r node records height R width words h665
  have bz : b.stacks 649=unary (node*r) := nodeStart_address a ra rd rc r node records height R width words
  have bp : b.stacks 660=BucketTupleProgram.Representative.tuplesBits [[]] :=
    nodeStart_tuples a ra rd rc r node records height R width words h660
  have bc : b.stacks 648=unary r := nodeStart_count a ra rd rc r node records height R width words
  obtain ⟨tables,costs,tl,c,htables,htlen,hclen,hel,htl,hend,hcp,hcz,hcf,htrace⟩ :=
    headLoop_measured entry b n N records.length W rows low bn bN bW brows blow bD bm hw hsize
      Valid Rel T B (hc ra rd rc words hcache) hv b (node*r) [[]] (loopFrame_refl b) bz bp
  have tablesLen : tables.length=r := by simpa [bc,unary] using htlen
  have costsLen : costs.length=r := hclen.trans tablesLen
  have cn : c.stacks 128=unary n :=
    (hcf 128 (by decide) (by simp [loopMutable])).trans bn
  have valid : ∀ heads∈enumerate tables,∀ h∈heads,
      BucketTupleProgram.Representative.Valid (unary n).length h := by
    simpa [unary] using BucketTupleProgram.enumerate_valid n tables (producedHeads_valid htables)
  obtain ⟨rf,tf,htf,hef⟩ := finalize_eval c (unary n) (enumerate tables) hcp cn valid
  let d := finalResult c rf (unary n) (enumerate tables)
  let e := clearManyState cleanupPorts d
  have hec := cleanup_eval d
  refine ⟨ra,rd,rc,words,tables,costs,_,e,hcache,htables,tablesLen,costsLen,
    hei.seq (hel.seq (hef.seq hec)),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hout := finalResult_value c rf (unary n) (enumerate tables)
    have hf163 := cleanup_frame d 163 (by decide)
    simpa [e,unary] using hf163.trans hout
  · intro i hi
    have hpi := external_protected hi
    have hcleanup : (i.val < 340 ∨ 628 ≤ i.val) ∧ (i.val < 640 ∨ 680 ≤ i.val) := by
      constructor <;> omega
    exact (cleanup_frame d i hcleanup).trans
      ((finalResult_frame c rf (unary n) (enumerate tables) i hpi hi.2.1).trans
        ((hcf i hpi (external_not_loop hi)).trans (bf i hpi (external_not_start hi))))
  · exact fun i hi=>cleanup_private d i hi
  · exact fun i=>cleanup_work d i

  · exact (cleanup_frame d 710 (by decide)).trans
      ((finalResult_frame c rf (unary n) (enumerate tables) 710 (by decide) (by decide)).trans
        ((hcf 710 (by decide) (by simp [loopMutable])).trans
          (nodeStart_positive a ra rd rc r node records height R width words)))

  · exact (cleanup_frame d 711 (by decide)).trans
      ((finalResult_frame c rf (unary n) (enumerate tables) 711 (by decide) (by decide)).trans
        ((hcf 711 (by decide) (by simp [loopMutable])).trans
          (nodeStart_negative a ra rd rc r node records height R width words)))

  · exact (cleanup_frame d 712 (by decide)).trans
      ((finalResult_frame c rf (unary n) (enumerate tables) 712 (by decide) (by decide)).trans
        ((hcf 712 (by decide) (by simp [loopMutable])).trans
          (nodeStart_denominator a ra rd rc r node records height R width words)))

  · refine ⟨c,rf,htrace,rfl,?_,hcp,cn⟩
    unfold nodeCost
    dsimp [d]
    omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
