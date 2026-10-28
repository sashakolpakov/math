import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBootRun

namespace OAI.Algorithms

/-! Initialization of one node's physical Cartesian head loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def nodeStart (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) : Data :=
  tupleInitialized (retainedState (bootState a ra rd rc r t records height R width words))

def initializeCost (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) : ℕ :=
  bootCost a ra rd rc r t records height R width words+
    retainCost (bootState a ra rd rc r t records height R width words)+8

theorem initialize_eval (a : Data) (r t : ℕ) (records : List (List Bool))
    (height R width : List Bool)
    (hr : a.stacks 130=List.replicate r true) (ht : a.stacks 307=List.replicate t true)
    (hrecords : a.stacks 136=SubexponentialSAT.Encoding.encodeList id records)
    (hheight : a.stacks 139=height) (hR : a.stacks 138=R) (hwidth : a.stacks 140=width)
    (hw : 1+2*height.length*R.length ≤ width.length) :
    ∃ ra rd rc words steps, steps ≤ initializeCost a ra rd rc r t records height R width words ∧
      Eval initializeNode steps a (nodeStart a ra rd rc r t records height R width words) ∧
      words.length=R.length ∧ (∀ w∈words,w.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range R.length).map (LayoutCoefficientRecurrence.H height.length) := by
  obtain ⟨ra,rd,rc,words,steps,hs,he,hl,hws,hvs⟩ :=
    boot_eval a r t records height R width hr ht hrecords hheight hR hwidth hw
  let b := bootState a ra rd rc r t records height R width words
  refine ⟨ra,rd,rc,words,_,?_,he.seq ((retainCache_eval b).seq (tupleInit_eval (retainedState b))),
    hl,hws,hvs⟩
  unfold initializeCost
  dsimp [b]
  omega

theorem nodeStart_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649,660,665,710,711,712] : List (Fin 768))) :
    (nodeStart a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  have h659 : i≠659 := hi.2
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  obtain ⟨h640,h641,h642,h643,h647,h648,h649,h660,h665,h710,h711,h712⟩ := hne
  simp only [nodeStart,tupleInitialized,Function.update_of_ne h665,Function.update_of_ne h660]
  rw [retainedState_frame _ i h659 h710 h711 h712]
  apply bootState_frame a ra rd rc r t records height R width words i hi
  simp [h640,h641,h642,h643,h647,h648,h649]

theorem nodeStart_count (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (nodeStart a ra rd rc r t records height R width words).stacks 648=List.replicate r true := by
  simp only [nodeStart,tupleInitialized,Function.update_of_ne (show (648:Fin 768)≠665 by decide),
    Function.update_of_ne (show (648:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 648 (by decide) (by decide) (by decide) (by decide)]
  exact bootState_count a ra rd rc r t records height R width words

theorem nodeStart_address (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (nodeStart a ra rd rc r t records height R width words).stacks 649=List.replicate (t*r) true := by
  simp only [nodeStart,tupleInitialized,Function.update_of_ne (show (649:Fin 768)≠665 by decide),
    Function.update_of_ne (show (649:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 649 (by decide) (by decide) (by decide) (by decide)]
  exact bootState_address a ra rd rc r t records height R width words

theorem nodeStart_dimension (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (nodeStart a ra rd rc r t records height R width words).stacks 647=List.replicate records.length true := by
  simp only [nodeStart,tupleInitialized,Function.update_of_ne (show (647:Fin 768)≠665 by decide),
    Function.update_of_ne (show (647:Fin 768)≠660 by decide)]
  rw [retainedState_frame _ 647 (by decide) (by decide) (by decide) (by decide)]
  exact bootState_dimension a ra rd rc r t records height R width words

theorem nodeStart_tuples (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (h660 : a.stacks 660=[]) :
    (nodeStart a ra rd rc r t records height R width words).stacks 660=
      BucketTupleProgram.Representative.tuplesBits [[]] := by
  have hb := bootState_frame a ra rd rc r t records height R width words 660 (by decide) (by simp)
  have hc := retainedState_frame (bootState a ra rd rc r t records height R width words)
    660 (by decide) (by decide) (by decide) (by decide)
  simp [nodeStart,tupleInitialized,hc,hb,h660,BucketTupleProgram.Representative.tuplesBits,
    BucketTupleProgram.Representative.headsBits,Encoding.encodeList,Encoding.frame]

theorem nodeStart_marker (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (h665 : a.stacks 665=[]) :
    (nodeStart a ra rd rc r t records height R width words).stacks 665=[false] := by
  have hb := bootState_frame a ra rd rc r t records height R width words 665 (by decide) (by simp)
  have hc := retainedState_frame (bootState a ra rd rc r t records height R width words)
    665 (by decide) (by decide) (by decide) (by decide)
  simp [nodeStart,tupleInitialized,hc,hb,h665]


theorem nodeStart_positive (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (nodeStart a ra rd rc r t records height R width words).stacks 710=
      words.flatten++a.stacks 710 := by
  simp only [nodeStart,tupleInitialized,
    Function.update_of_ne (show (710:Fin 768)≠665 by decide),
    Function.update_of_ne (show (710:Fin 768)≠660 by decide),retainedState_positive_append]
  rw [bootState_positive,bootState_frame a ra rd rc r t records height R width words 710 (by decide) (by simp)]


theorem nodeStart_negative (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (nodeStart a ra rd rc r t records height R width words).stacks 711=
      List.replicate (R.length*width.length) false++a.stacks 711 := by
  simp only [nodeStart,tupleInitialized,
    Function.update_of_ne (show (711:Fin 768)≠665 by decide),
    Function.update_of_ne (show (711:Fin 768)≠660 by decide),retainedState_negative_append]
  rw [bootState_negative,bootState_frame a ra rd rc r t records height R width words 711 (by decide) (by simp)]


theorem nodeStart_denominator (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) :
    (nodeStart a ra rd rc r t records height R width words).stacks 712=
      LayoutProgram.IntegerCache.denominatorWord R.length++a.stacks 712 := by
  simp only [nodeStart,tupleInitialized,
    Function.update_of_ne (show (712:Fin 768)≠665 by decide),
    Function.update_of_ne (show (712:Fin 768)≠660 by decide),retainedState_denominator_append]
  rw [bootState_denominator,bootState_frame a ra rd rc r t records height R width words 712 (by decide) (by simp)]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
