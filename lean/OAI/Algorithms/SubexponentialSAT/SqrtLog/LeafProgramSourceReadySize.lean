import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceReadyInput

namespace OAI.Algorithms

/-! Word bounds for the actual source preparation and full source initializer.
The bound explicitly includes the full (R+1)-coefficient zero array. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

variable {r Q d : ℕ} {p : SourceBank.Parameters r Q d}
  {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : Data} {v N f S : ℕ}

theorem Input.prepared_bound (h : Input p ps P a v N f S) : WordBound S (prepared a) := by
  have hsave : WordBound S (SourceStaging.saved a) := by
    apply clearMany_wordBound
    exact copyMany_wordBound SourceStaging.savePairs a S (by decide)
      (by intro q hq
          simp only [SourceStaging.savePairs,List.mem_cons,List.mem_nil_iff,or_false] at hq
          rcases hq with rfl|rfl|rfl|rfl <;> exact h.backups _ (by decide))
      (by simp [SourceStaging.savePairs]) h.size
  have hs : ∀ q ∈ SourceControls.pairs,
      q.2 ∉ SourceStaging.cachePorts ∧ q.2 ∉ SourceStaging.backupPorts := by
    simp [SourceControls.pairs,SourceStaging.cachePorts,SourceStaging.backupPorts]
  have hcopy : WordBound S (copyManyState SourceControls.pairs (SourceStaging.saved a)) :=
    copyMany_wordBound SourceControls.pairs (SourceStaging.saved a) S (by decide)
      (by intro q hq
          rw [saved_frame a q.2 (hs q hq).1 (hs q hq).2]
          exact h.controls_empty q hq)
      (by simp [SourceControls.pairs]) hsave
  intro i
  by_cases hi : i=365
  · subst i
    rw [prepared_delta a (h.clean 25 (by decide))]
    simp only [List.length_cons,List.length_nil]
    have := h.countSize
    omega
  · simpa only [prepared,SourceControls.prepared,SourceControls.delta_stacks,
      Function.update_of_ne hi] using hcopy i

theorem Input.local_bound (h : Input p ps P a v N f S) (i : Fin 340) :
    (localStore a i).length ≤ S := h.prepared_bound (localPort i)

theorem Input.base_bound (h : Input p ps P a v N f S) (i : Fin 340) :
    (sourceBase a (p.R+1) (d*baseWidth 3 p.t) ps v N f i).length ≤ S := by
  have upd (s : Fin 340 → List Bool) (hs : ∀ j,(s j).length ≤ S)
      (j : Fin 340) (b : List Bool) (hb : b.length ≤ S) :
      ∀ i,(Function.update s j b i).length ≤ S := by
    intro i
    by_cases hi : i=j
    · subst i; simpa using hb
    · simpa only [Function.update_of_ne hi] using hs i
  have hc : (List.replicate (p.R+1) true).length ≤ S := by simpa using h.countSize
  have hz : (List.replicate ((p.R+1)*(d*baseWidth 3 p.t)) false).length ≤ S := by
    simpa using h.arraySize
  have h1 := upd (localStore a) h.local_bound 243 _ hc
  have h2 := upd _ h1 242 _ hz
  have h3 := upd _ h2 192 _ hz
  have h4 := upd _ h3 193 _ hc
  have hidx : (LayoutSourcePlanLookup.unary (ps.idxOf (v,N+f))).length ≤ S := by
    simpa only [LayoutSourcePlanLookup.unary,List.length_replicate,List.idxOf,beq_eq_decide] using
      (List.idxOf_le_length (a := (v,N+f)) (l := ps)).trans h.incidenceBound
  exact upd _ h4 304 _ hidx i

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
