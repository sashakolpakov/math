import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceReadyBank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceReadySize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceNative

namespace OAI.Algorithms

/-! Physical master words and ordinary scratch cleanliness imply every native
source precondition. The numerator uses the cleared 5/10 view; the executor
keeps the original arithmetic words. No source execution is a hypothesis. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.low_empty (h : Input p ps P a v N f S) :
    ∀ i ∈ SourceStaging.lowClearPorts,a.stacks i=[] := by
  intro i hi
  obtain ⟨j,hj,hji⟩ := (SourceStaging.lowClear_iff i).mp hi
  rw [← hji]
  exact h.clean (Fin.castAdd 135 j) (by
    intro hp
    simp only [physicalLive, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|
      hp|hp|hp|hp|hp|hp|hp
    all_goals have hv := congrArg Fin.val hp
    all_goals simp at hv
    all_goals try omega
    all_goals apply hj
    all_goals simp [SourceStaging.retainedLow, Fin.ext_iff]
    all_goals omega)

theorem Input.extra_empty (h : Input p ps P a v N f S) :
    ∀ i ∈ SourceControls.extraPorts,a.stacks i=[] := by
  intro i hi
  have hb := (SourceControls.mem_extraPorts i).mp hi
  have hlo : 589 ≤ i.val := by omega
  have hhi : i.val < 680 := by omega
  let j : Fin 340 := ⟨i.val-340,by omega⟩
  have hj : 249 ≤ j.val := by dsimp [j]; omega
  have he : localPort j=i := by apply Fin.ext; dsimp [localPort,j]; omega
  rw [← he]
  apply h.clean
  intro hp
  simp [physicalLive] at hp
  omega

theorem Input.base_empty (h : Input p ps P a v N f S) (D W : ℕ) (i : Fin 340)
    (hb : localBlank i) (hi : i ∉ ([192,193,242,243,304] : List (Fin 340))) :
    sourceBase a D W ps v N f i=[] :=
  (base_frame a D W ps v N f i hi).trans (h.empty i hb)

theorem Input.native (h : Input p ps P a v N f S) :
    Source.NativeInput p ps P a v N f S (rawLow a 10) (fun _ => []) := by
  have E := h.empty
  have BE := h.base_empty (p.R+1) (d*baseWidth 3 p.t)
  have IE (i : Fin 340) (hb : localBlank i)
      (hi : i ∉ ([192,193,242,243] : List (Fin 340))) :
      initializeFinish (localStore a) (p.R+1) (d*baseWidth 3 p.t) i=[] := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at hi
    simpa only [initializeFinish,Function.update_of_ne hi.1,
      Function.update_of_ne hi.2.1,Function.update_of_ne hi.2.2.1,
      Function.update_of_ne hi.2.2.2] using E i hb
  refine {
    tmp := h.tmp
    low := h.low_empty
    extra := h.extra_empty
    backups := h.backups
    init := initialized_ready p.model p.modulus p.cache a (p.R+1) h.arithmetic
      h.dimension (h.clean 245 (by decide))
    literal := (local_frame a 233 (by decide)).trans h.literal
    ambient := (local_frame a 212 (by decide)).trans h.ambient
    factor := (local_frame a 216 (by decide)).trans h.factor
    plans := (h.copied 136 337 (by decide)).trans h.plans
    lookup := ?_
    rowsClean := ?_
    workClean := ?_
    owner := ?_
    arithmetic := arithmetic_ready p.model p.modulus p.cache a h.arithmetic
    empty := ?_
    source := h.bank_ready (p.R+1) (d*baseWidth 3 p.t)
    sourceClean := ?_
    metadata := (h.copied 135 306 (by decide)).trans h.metadata
    size := ?_
    metadataSize := h.metadataSize
    incidenceBound := h.incidenceBound
    nodesBound := ?_
    radiusBound := Nat.le_trans (Nat.le_succ _) h.countSize
    ringWidthBound := ?_
    rowWidthBound := ?_
  }
  · intro i hi
    have hb : localBlank i := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [localBlank, physicalLive, changedLocal]
    have hn : i ∉ ([192,193,242,243] : List (Fin 340)) := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    exact IE i hb hn
  · intro i hi
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply BE <;> simp [localBlank, physicalLive, changedLocal]
  · intro i hi
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply BE <;> simp [localBlank, physicalLive, changedLocal]
  · intro i hi
    fin_cases i <;> norm_num at hi
    all_goals apply BE <;> simp [ownerStacks, localBlank, physicalLive, changedLocal]
  · exact ⟨E 99 (by decide),E 121 (by decide),E 122 (by decide),E 240 (by decide),
      E 241 (by decide),E 244 (by decide),E 245 (by decide),fun i => by
        fin_cases i <;> apply E <;>
          simp [bufferPorts, executorPorts, localBlank, physicalLive, changedLocal]⟩
  · intro i hi
    simp only [SourceBank.cleanupPorts, List.mem_append] at hi
    rcases hi with ((hi | hi) | hi) | hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        apply BE <;> simp [sourcePorts, localBlank, physicalLive, changedLocal]
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
      fin_cases k <;> apply BE <;>
        simp [sourcePorts, localBlank, physicalLive, changedLocal]
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
      fin_cases k <;> apply BE <;>
        simp [sourcePorts, localBlank, physicalLive, changedLocal]
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl <;>
        apply BE <;> simp [sourcePorts, localBlank, physicalLive, changedLocal]
  · intro i; exact h.base_bound (sourcePorts i)
  · simpa only [h.nodes,List.length_replicate] using h.size 131
  · simpa only [h.ringWidth] using h.size 717
  · simpa only [h.rowWidth] using h.size 716

/-- The two extra source-call word bounds used by the incidence assembly are
also consequences of the same actual byte-size bound. -/
theorem Input.call_bounds (h : Input p ps P a v N f S) :
    (Source.nativeStore a 21).length ≤ S ∧ (Source.nativeStore a 26).length ≤ S :=
  ⟨h.local_bound 21,h.local_bound 26⟩

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
