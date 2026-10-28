import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceReadyArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramAssembly
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramStaging
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceConfiguration

namespace OAI.Algorithms

/-! A physical caller contract. All hypotheses are bytes in retained masters,
blank work tapes, or explicit length bounds. In particular no native source
readiness or execution is assumed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Arithmetic masters, incidence masters, and the three running literal-loop
words are allowed to be populated before source preparation. -/
def physicalLive : List (Fin 340) :=
  [5,10,104,192,193,194,201,202,203,204,206,207,208,209,210,211,212,213,
   215,216,229,233,234,235,243]

def localBlank (i : Fin 340) : Prop :=
  (i ∉ physicalLive ∧ i ∉ changedLocal) ∨ i ∈ ([192,193,242,243] : List (Fin 340))
instance (i : Fin 340) : Decidable (localBlank i) := inferInstanceAs
  (Decidable ((i ∉ physicalLive ∧ i ∉ changedLocal) ∨
    i ∈ ([192,193,242,243] : List (Fin 340))))

structure Input {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : Data) (v N f S : ℕ) : Prop where
  arithmetic : PerturbationAssembly.ArithmeticInput p.t p.model p.modulus p.cache (rawLow a)
  clean : ∀ i : Fin 340,i ∉ physicalLive → a.stacks (localPort i)=[]
  tmp : a.stacks 684=[]
  backups : ∀ i ∈ SourceStaging.backupPorts,a.stacks i=[]
  dimension : a.stacks (localPort 210)=List.replicate (p.R+1) true
  ambient : a.stacks (localPort 212)=LayoutSourcePlanLookup.unary N
  factor : a.stacks (localPort 216)=LayoutSourcePlanLookup.unary f
  literal : a.stacks (localPort 233)=LayoutSourcePlanLookup.unary v
  colors : a.stacks 130=List.replicate r true
  nodes : a.stacks 131=List.replicate Q true
  typeWidth : a.stacks 132=List.replicate (Q*r) true
  positive : a.stacks 710=p.saved.hp
  negative : a.stacks 711=p.saved.hn
  scalarWidth : a.stacks 140=p.width
  power : a.stacks 712=p.power.1
  powerNegative : p.power.2=[]
  radius : a.stacks 138=List.replicate p.R true
  offset : a.stacks 139=p.aWord
  metadata : a.stacks 135=SelectorProgram.rawRecords (PackingMetadata.records P (fun v => List.replicate v.val true) CollisionProgram.encodeType)
  plans : a.stacks 136=LayoutOwnerFiberProgram.stream ps
  inverses : a.stacks 713=(List.ofFn (fun i => RingProgram.flat (p.inverse i))).flatten
  negatives : a.stacks 714=(List.ofFn (fun i => RingProgram.flat (p.negative i))).flatten
  differences : a.stacks 715=(List.ofFn (fun i =>
    (List.ofFn (fun j => RingProgram.flat (p.difference i j))).flatten)).flatten
  ringWidth : a.stacks 717=p.ringWidth
  rowWidth : a.stacks 716=p.rowWidth
  zero : a.stacks 280=RingProgram.flat p.ops.zeroRun.1
  one : a.stacks 207=RingProgram.flat p.ops.oneRun.1
  minusOne : a.stacks 211=RingProgram.flat p.minusOne
  inverseDenominator : a.stacks 728=RingProgram.flat p.invDenom
  size : ∀ i : Fin 768,(a.stacks i).length ≤ S
  arraySize : (p.R+1)*(d*baseWidth 3 p.t) ≤ S
  countSize : p.R+1 ≤ S
  metadataSize : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S
  incidenceBound : ps.length ≤ S

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.controls_empty (h : Input p ps P a v N f S) :
    ∀ q ∈ SourceControls.pairs,a.stacks q.2=[] := by
  intro q hq
  simp only [SourceControls.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h.clean 21 (by decide)
  · exact h.clean 22 (by decide)
  · exact h.clean 26 (by decide)
  · exact h.clean 42 (by decide)
  · exact h.clean 43 (by decide)
  · exact h.clean 44 (by decide)
  · exact h.clean 45 (by decide)
  · exact h.clean 47 (by decide)
  · exact h.clean 48 (by decide)
  · exact h.clean 306 (by decide)
  · exact h.clean 308 (by decide)
  · exact h.clean 309 (by decide)
  · exact h.clean 310 (by decide)
  · exact h.clean 311 (by decide)
  · exact h.clean 312 (by decide)
  · exact h.clean 313 (by decide)
  · exact h.clean 314 (by decide)
  · exact h.clean 337 (by decide)
  · exact h.clean 249 (by decide)
  · exact h.clean 250 (by decide)
  · exact h.clean 251 (by decide)
  · exact h.clean 252 (by decide)

theorem Input.empty (h : Input p ps P a v N f S) (i : Fin 340) (hi : localBlank i) :
    localStore a i=[] := by
  rcases hi with hi|hi
  · exact (local_frame a i hi.2).trans (h.clean i hi.1)
  · exact local_cache a i hi

theorem Input.copied (h : Input p ps P a v N f S) (src : Fin 768) (dst : Fin 340)
    (hp : (src,localPort dst) ∈ SourceControls.pairs) :
    localStore a dst=a.stacks src := local_copy a h.controls_empty src dst hp

theorem Input.delta (h : Input p ps P a v N f S) : localStore a 25=[true] :=
  prepared_delta a (h.clean 25 (by decide))

def sourceBase (a : Data) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ) :=
  preparedSourceStore (localStore a) D W ps v N f

def bank (a : Data) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ) : SourceBank.Data :=
  ⟨fun _ => false,clearedSourceStore (sourceBase a D W ps v N f) ∘ sourcePorts⟩

theorem base_frame (a : Data) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ)
    (i : Fin 340) (hi : i ∉ ([192,193,242,243,304] : List (Fin 340))) :
    sourceBase a D W ps v N f i=localStore a i := by
  simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hi
  simp [sourceBase,preparedSourceStore,initializeFinish,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2]

theorem bank_frame (a : Data) (D W : ℕ) (ps : List (ℕ × ℕ)) (v N f : ℕ)
    (i : Fin 320) (hi : i ∉ ([5,10,192,193,242,243,304] : List (Fin 320))) :
    (bank a D W ps v N f).stacks i=localStore a (sourcePorts i) := by
  have hh : sourcePorts i ∉ ([192,193,242,243,304] : List (Fin 340)) := by
    simpa [sourcePorts,Fin.ext_iff] using (by
      simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hi ⊢
      exact hi.2.2 : i ∉ ([192,193,242,243,304] : List (Fin 320)))
  have h5 : sourcePorts i≠5 := by
    intro he; have hh : i=5 := Fin.ext (congrArg (fun j : Fin 340 => j.val) he)
    exact hi (by simp [hh])
  have h10 : sourcePorts i≠10 := by
    intro he; have hh : i=10 := Fin.ext (congrArg (fun j : Fin 340 => j.val) he)
    exact hi (by simp [hh])
  simp only [bank,Function.comp_apply,clearedSourceStore,Function.update_of_ne h5,
    Function.update_of_ne h10]
  exact base_frame a D W ps v N f _ hh

def bankBlank (i : Fin 320) : Prop := i=5 ∨ i=10 ∨
  (localBlank (sourcePorts i) ∧ i ∉ ([192,193,242,243,304] : List (Fin 320)))
instance (i : Fin 320) : Decidable (bankBlank i) := inferInstanceAs
  (Decidable (i=5 ∨ i=10 ∨
    (localBlank (sourcePorts i) ∧ i ∉ ([192,193,242,243,304] : List (Fin 320)))))

theorem Input.bank_empty (h : Input p ps P a v N f S) (D W : ℕ) (i : Fin 320)
    (hi : bankBlank i) : (bank a D W ps v N f).stacks i=[] := by
  rcases hi with rfl|rfl|hi
  · simp [bank,clearedSourceStore,sourcePorts]
  · simp [bank,clearedSourceStore,sourcePorts]
  · by_cases h5 : i=5
    · subst i; simp [bank,clearedSourceStore,sourcePorts]
    by_cases h10 : i=10
    · subst i; simp [bank,clearedSourceStore,sourcePorts]
    rw [bank_frame a D W ps v N f i (by simpa [h5,h10] using hi.2)]
    exact h.empty _ hi.1

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
