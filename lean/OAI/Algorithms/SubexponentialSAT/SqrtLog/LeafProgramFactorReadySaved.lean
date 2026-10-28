import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadyCaps

namespace OAI.Algorithms

/-! Assignment setup saves the two incoming accumulators at146/147. Changing
these buffers preserves all factor readiness when their byte bounds are paid. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorReady
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram SubexpSetupStorage
open PerturbationAssembly SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native IdempotentApplyProgram.Steps
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def put (a : State 16 768) (i : Fin 768) (w : List Bool) : State 16 768 :=
  ⟨a.regs,Function.update a.stacks i w⟩

theorem copyState_put (a : State 16 768) (i src dst : Fin 768) (w : List Bool)
    (hs : i≠src) (hd : i≠dst) :
    copyState src dst (put a i w)=put (copyState src dst a) i w := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    have hs' : src≠i := Ne.symm hs
    have hd' : dst≠i := Ne.symm hd
    by_cases hj : j=i
    · subst j; simp [put,copyState,StackRoutines.copyStacks,hd,hs',hd']
    · by_cases hdst : j=dst
      · subst j; simp [put,copyState,StackRoutines.copyStacks,hs',hd']
      · simp [put,copyState,StackRoutines.copyStacks,hj,hdst,hs',hd']

theorem copyMany_put (ps : List (Fin 768 × Fin 768)) (a : State 16 768)
    (i : Fin 768) (w : List Bool) (hi : ∀ p∈ps,i≠p.1 ∧ i≠p.2) :
    copyManyState ps (put a i w)=put (copyManyState ps a) i w := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    rw [copyManyState,copyState_put a i p.1 p.2 w (hi p (by simp)).1 (hi p (by simp)).2]
    exact ih _ (fun q hq=>hi q (by simp [hq]))

theorem staged_put (a : State 16 768) (i : Fin 768) (w : List Bool)
    (hi : i=146 ∨ i=147) : Incidence.staged (put a i w)=put (Incidence.staged a) i w := by
  have hps : ∀ p∈Incidence.pairs,i≠p.1 ∧ i≠p.2 := by
    intro p hp
    simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals rcases hi with rfl|rfl <;> decide
  have h138 : i≠138 := by rcases hi with rfl|rfl <;> decide
  have h550 : i≠550 := by rcases hi with rfl|rfl <;> decide
  unfold Incidence.staged
  rw [copyMany_put _ _ _ _ hps]
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    have h138' : (138 : Fin 768)≠i := Ne.symm h138
    have h550' : (550 : Fin 768)≠i := Ne.symm h550
    by_cases hj : j=i
    · subst j; simp [put,SourceControls.cutoffState,h550,h138',h550']
    · by_cases hc : j=550
      · subst j; simp [put,SourceControls.cutoffState,h138',h550']
      · simp [put,SourceControls.cutoffState,hj,hc,h138',h550']

def savedWords (base : Fin 768 → List Bool) (left right : List Bool) :=
  Function.update (Function.update base 146 left) 147 right

def saved (a : State 16 768) (left right : List Bool) : State 16 768 :=
  ⟨a.regs,savedWords a.stacks left right⟩

theorem staged_saved (a : State 16 768) (left right : List Bool) :
    Incidence.staged (saved a left right)=saved (Incidence.staged a) left right := by
  change Incidence.staged (put (put a 146 left) 147 right)=_
  rw [staged_put _ 147 right (Or.inr rfl),staged_put a 146 left (Or.inl rfl)]
  rfl

theorem saved_bound (base : Fin 768 → List Bool) (left right : List Bool) (A : ℕ)
    (hb : ∀ i,(base i).length ≤ A) (hl : left.length ≤ A) (hr : right.length ≤ A) :
    ∀ i,(savedWords base left right i).length ≤ A := by
  intro i
  by_cases h146 : i=146
  · subst i; simpa [savedWords] using hl
  · by_cases h147 : i=147
    · subst i; simpa [savedWords] using hr
    · simpa [savedWords,h146,h147] using hb i

theorem saved_frame (a : State 16 768) (left right : List Bool) (i : Fin 768)
    (h146 : i≠146) (h147 : i≠147) :
    (saved a left right).stacks i=a.stacks i := by simp [saved,savedWords,h146,h147]

variable {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A : ℕ} {base : Fin 768 → List Bool}

private theorem executorPort_ne_146 : ∀ i : Fin 256,
    SourceReady.localPort (LayoutSourceRowsProgram.executorPorts i) ≠ 146 := by
  intro i he
  have hv := congrArg Fin.val he
  simp [SourceReady.localPort, LayoutSourceRowsProgram.executorPorts] at hv
  omega

private theorem executorPort_ne_147 : ∀ i : Fin 256,
    SourceReady.localPort (LayoutSourceRowsProgram.executorPorts i) ≠ 147 := by
  intro i he
  have hv := congrArg Fin.val he
  simp [SourceReady.localPort, LayoutSourceRowsProgram.executorPorts] at hv
  omega

private theorem localPort_ne_146 : ∀ i : Fin 340, SourceReady.localPort i ≠ 146 := by
  intro i he
  have hv := congrArg Fin.val he
  simp [SourceReady.localPort] at hv
  omega

private theorem localPort_ne_147 : ∀ i : Fin 340, SourceReady.localPort i ≠ 147 := by
  intro i he
  have hv := congrArg Fin.val he
  simp [SourceReady.localPort] at hv
  omega

private theorem backupPorts_ne : ∀ i ∈ SourceStaging.backupPorts,
    i ≠ 146 ∧ i ≠ 147 := by
  intro i hi
  simp only [SourceStaging.backupPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl <;> norm_num

private theorem dispatchScratch_ne : ∀ i ∈ FactorDispatch.scratch,
    i ≠ 146 ∧ i ≠ 147 := by
  intro i hi
  simp only [FactorDispatch.scratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num

private theorem blankPorts_ne :
    ∀ i ∈ ([154,63,64,67,68,62,556,684,159] : List (Fin 768)),
      i ≠ 146 ∧ i ≠ 147 := by
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

private theorem expansionScratch_ne : ∀ i ∈ Expansion.scratch,
    i ≠ 146 ∧ i ≠ 147 := by
  intro i hi
  simp only [Expansion.scratch, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl <;> norm_num

theorem source_saved {a : State 16 768} {v f : ℕ}
    (h : SourceReady.Input q.p q.ps q.packing a v n f S) (left right : List Bool)
    (hl : left.length ≤ S) (hr : right.length ≤ S) :
    SourceReady.Input q.p q.ps q.packing (saved a left right) v n f S := by
  have H := saved_frame a left right
  constructor
  · apply h.arithmetic.frame_low
    intro i hi
    exact H _ (executorPort_ne_146 i)
      (executorPort_ne_147 i)
  · intro i hi
    exact (H _ (localPort_ne_146 i)
      (localPort_ne_147 i)).trans (h.clean i hi)
  · exact (H _ (by decide) (by decide)).trans h.tmp
  · intro i hi
    have hn := backupPorts_ne i hi
    exact (H i hn.1 hn.2).trans (h.backups i hi)
  · exact (H _ (by decide) (by decide)).trans h.dimension
  · exact (H _ (by decide) (by decide)).trans h.ambient
  · exact (H _ (by decide) (by decide)).trans h.factor
  · exact (H _ (by decide) (by decide)).trans h.literal
  · exact (H _ (by decide) (by decide)).trans h.colors
  · exact (H _ (by decide) (by decide)).trans h.nodes
  · exact (H _ (by decide) (by decide)).trans h.typeWidth
  · exact (H _ (by decide) (by decide)).trans h.positive
  · exact (H _ (by decide) (by decide)).trans h.negative
  · exact (H _ (by decide) (by decide)).trans h.scalarWidth
  · exact (H _ (by decide) (by decide)).trans h.power
  · exact h.powerNegative
  · exact (H _ (by decide) (by decide)).trans h.radius
  · exact (H _ (by decide) (by decide)).trans h.offset
  · exact (H _ (by decide) (by decide)).trans h.metadata
  · exact (H _ (by decide) (by decide)).trans h.plans
  · exact (H _ (by decide) (by decide)).trans h.inverses
  · exact (H _ (by decide) (by decide)).trans h.negatives
  · exact (H _ (by decide) (by decide)).trans h.differences
  · exact (H _ (by decide) (by decide)).trans h.ringWidth
  · exact (H _ (by decide) (by decide)).trans h.rowWidth
  · exact (H _ (by decide) (by decide)).trans h.zero
  · exact (H _ (by decide) (by decide)).trans h.one
  · exact (H _ (by decide) (by decide)).trans h.minusOne
  · exact (H _ (by decide) (by decide)).trans h.inverseDenominator
  · exact saved_bound a.stacks left right S h.size hl hr
  · exact h.arraySize
  · exact h.countSize
  · exact h.metadataSize
  · exact h.incidenceBound

theorem caller_saved {a : State 16 768}
    (h : CallerInput q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R q.theta a n)
    (left right : List Bool) :
    CallerInput q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R q.theta (saved a left right) n := by
  have H := saved_frame a left right
  constructor
  · exact h.widthPositive
  · exact h.zeroCanonical
  · exact h.zeroBits
  · exact (H _ (by decide) (by decide)).trans h.modulus
  · rw [H _ (by decide) (by decide)]; exact h.width
  · exact (H _ (by decide) (by decide)).trans h.zero
  · exact (H _ (by decide) (by decide)).trans h.table
  · rw [H _ (by decide) (by decide)]; exact h.degree
  · rw [H _ (by decide) (by decide)]; exact h.choicesLength
  · exact (H _ (by decide) (by decide)).trans h.zeroWord
  · exact (H _ (by decide) (by decide)).trans h.oneWord
  · exact (H _ (by decide) (by decide)).trans h.thetaWord
  · exact (H _ (by decide) (by decide)).trans h.ambientCount
  · exact (H _ (by decide) (by decide)).trans h.targetCount
  · exact (H _ (by decide) (by decide)).trans h.radius
  · rw [H _ (by decide) (by decide)]; exact h.highLength
  · intro i hi hj hn
    have h146 : i≠146 := by intro he; subst i; norm_num at hi
    have h147 : i≠147 := by intro he; subst i; norm_num at hi
    exact (H i h146 h147).trans (h.workerEmpty i hi hj hn)

theorem Input.update_saved (h : Input q S A base) {left right : List Bool}
    (hAS : A ≤ S) (hl : left.length ≤ A) (hr : right.length ≤ A) :
    Input q S A (savedWords base left right) := by
  have H (i : Fin 768) (h146 : i≠146) (h147 : i≠147) :
      savedWords base left right i=base i := by simp [savedWords,h146,h147]
  constructor
  · exact caller_saved h.caller left right
  · change SourceReady.Input _ _ _ (Incidence.staged (saved (baseData base) left right)) _ _ _ _
    rw [staged_saved]
    exact source_saved h.physical left right (hl.trans hAS) (hr.trans hAS)
  · exact saved_bound base left right A h.size hl hr
  · change WordBound A (Incidence.staged (saved (baseData base) left right))
    rw [staged_saved]
    exact saved_bound _ left right A h.stagedSize hl hr
  · exact (H _ (by decide) (by decide)).trans h.rows
  · exact (H _ (by decide) (by decide)).trans h.clauses
  · exact (H _ (by decide) (by decide)).trans h.count
  · exact (H _ (by decide) (by decide)).trans h.mark
  · exact (H _ (by decide) (by decide)).trans h.flag
  · intro i hi
    have hn := dispatchScratch_ne i hi
    exact (H i hn.1 hn.2).trans (h.dispatchWork i hi)
  · intro i hi
    have hn := blankPorts_ne i hi
    exact (H i hn.1 hn.2).trans (h.blank i hi)
  · rw [H _ (by decide) (by decide)]; exact h.hashWidth
  · rw [H _ (by decide) (by decide)]; exact h.hashModulus
  · intro i hi
    have hn := expansionScratch_ne i hi
    exact (H i hn.1 hn.2).trans (h.expand i hi)
  · exact (H _ (by decide) (by decide)).trans h.work358
  · exact (H _ (by decide) (by decide)).trans h.work359
  · intro i
    exact (H _ ((by decide : ∀ i : Fin 56,Factor.nativeStacks (Memory.lowPort i)≠146) i)
      ((by decide : ∀ i : Fin 56,Factor.nativeStacks (Memory.lowPort i)≠147) i)).trans (h.low i)
  · exact (H _ (by decide) (by decide)).trans h.one
  · exact (H _ (by decide) (by decide)).trans h.minus
  · exact (H _ (by decide) (by decide)).trans h.tape
  · rw [H _ (by decide) (by decide)]; exact h.shape
  · intro i hi
    have hn := (by decide : ∀ i∈FactorServices.indicatorScratch,
      Factor.indicatorStacks i≠146 ∧ Factor.indicatorStacks i≠147) i hi
    exact (H _ hn.1 hn.2).trans (h.indicatorWork i hi)
  · intro i hi
    have hn := (by decide : ∀ i∈FactorServices.clauseScratch,
      Clause.callerStacks i≠146 ∧ Clause.callerStacks i≠147) i hi
    exact (H _ hn.1 hn.2).trans (h.clauseWork i hi)

theorem Limits.base_le_source {T F : ℕ} (h : Limits q S A T F) : A ≤ S := by
  have hh := h.live
  unfold callBound wordBound at hh
  omega

theorem Resources.update_saved {F Z : ℕ} (h : Resources q base F Z) (left right : List Bool) :
    Resources q (savedWords base left right) F Z := by
  exact ⟨h.native,h.ids,h.width,h.source,h.terms,h.digits,h.clauseWidths,h.payload,
    by simpa [savedWords] using h.modulus⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorReady

end OAI.Algorithms
