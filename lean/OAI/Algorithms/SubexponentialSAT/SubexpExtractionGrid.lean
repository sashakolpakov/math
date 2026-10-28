import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExtractionJobProgram
import OAI.Algorithms.SubexponentialSAT.UnaryGridProgram

namespace OAI.Algorithms

/-! Actual generation of all U/Z extraction records for one captured moment
source.  A single source frame is cached outside the two unary loops. -/

namespace SubexponentialSAT.SubexpExtractionGrid

open BitProgram StructuredCalls
open scoped BigOperators

abbrev Data := SubexpExtractionJobProgram.Data
abbrev Code := SubexpExtractionJobProgram.Code
abbrev Job := SubexpMomentProgram.Job

def step (xs source : List Bool) (width u z : ℕ) (out : List Bool) : List Bool :=
  true :: (Encoding.frame (SubexpExtractionJobProgram.job xs source u z width).encode ++ out)

def callbackCost (xs source : List Bool) (width u z : ℕ) : ℕ :=
  100 * (xs.length + source.length + u + z + width + 2)

theorem callback_spec (base : Data) (xs source : List Bool) (width : ℕ)
    (h : SubexpExtractionJobProgram.Ready base xs source 0 0 width) :
    UnaryGridProgram.CallbackSpec SubexpExtractionJobProgram.emitOne
      (step xs source width) (callbackCost xs source width) base := by
  intro u z d hf hu hz
  have ready : SubexpExtractionJobProgram.Ready d xs source u z width := by
    constructor
    · exact (hf 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.x
    · exact (hf 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.source
    · exact hu
    · exact hz
    · exact (hf 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.width
    · exact (hf 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.raw
    · exact (hf 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.counter
    · exact (hf 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.key
    · exact (hf 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.temporary
    · exact (hf 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.inner
    · exact (hf 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.cached
  exact SubexpExtractionJobProgram.emitOne_eval d xs source u z width ready

def gridCost (xs source : List Bool) (D width : ℕ) : ℕ :=
  D * (D + 1) * (100 * (xs.length + source.length + 2 * D + width + 2)) +
    13 * D ^ 2 + 31 * D + 10

theorem gridCost_bound (xs source : List Bool) (D width : ℕ) :
    UnaryGridProgram.gridBound (callbackCost xs source width) D ≤ gridCost xs source D width := by
  apply UnaryGridProgram.gridBound_le_uniform
  intro u z hu hz
  dsimp [callbackCost]
  omega

def work : List (Fin 24) := [4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 17]

structure Input (d : Data) (xs source : List Bool) (D width : ℕ) : Prop where
  x : d.stacks 0 = xs
  source : d.stacks 1 = source
  dimension : d.stacks 2 = List.replicate D true
  width : d.stacks 3 = List.replicate width true
  clean : ∀ i ∈ work, d.stacks i = []

theorem prepared_ready (d : Data) (xs source : List Bool) (D width : ℕ)
    (h : Input d xs source D width) :
    SubexpExtractionJobProgram.Ready (SubexpJobFrames.sourceResult d) xs source 0 0 width := by
  have hp := SubexpJobFrames.sourceResult_preserved d
  have hc := SubexpJobFrames.sourceResult_clean d
  constructor
  · exact (hp 0 (by decide) (by decide) (by decide)).trans h.x
  · exact (hp 1 (by decide) (by decide) (by decide)).trans h.source
  · simpa using (hp 4 (by decide) (by decide) (by decide)).trans (h.clean 4 (by decide))
  · simpa using (hp 5 (by decide) (by decide) (by decide)).trans (h.clean 5 (by decide))
  · exact (hp 3 (by decide) (by decide) (by decide)).trans h.width
  · exact (hp 8 (by decide) (by decide) (by decide)).trans (h.clean 8 (by decide))
  · exact (hp 9 (by decide) (by decide) (by decide)).trans (h.clean 9 (by decide))
  · exact hc.1
  · exact (hp 11 (by decide) (by decide) (by decide)).trans (h.clean 11 (by decide))
  · exact (hp 12 (by decide) (by decide) (by decide)).trans (h.clean 12 (by decide))
  · rw [SubexpJobFrames.sourceResult_frame d (h.clean 10 (by decide))
      (h.clean 15 (by decide)) (h.clean 17 (by decide)), h.source]

def command : Code := .seq SubexpJobFrames.prepareSource
  (.seq (UnaryGridProgram.command SubexpExtractionJobProgram.emitOne) (UnaryGridProgram.clear 15))

def program := StructuredCalls.compiled command 0 14

theorem command_eval (d : Data) (xs source : List Bool) (D width : ℕ)
    (h : Input d xs source D width) :
    ∃ ticks e, ticks ≤ gridCost xs source D width + 19 * source.length + 21 ∧
      Eval command ticks d e ∧
      e.stacks = Function.update d.stacks 14
        (UnaryGridProgram.gridOutput (step xs source width) D D (d.stacks 14)) := by
  let b := SubexpJobFrames.sourceResult d
  have hb := prepared_ready d xs source D width h
  have hprep := SubexpJobFrames.prepareSource_eval d (h.clean 11 (by decide))
  have hbD : (b.stacks 2).length = D := by
    rw [SubexpJobFrames.sourceResult_preserved d 2 (by decide) (by decide) (by decide),
      h.dimension, List.length_replicate]
  have hb6 : b.stacks 6 = [] :=
    (SubexpJobFrames.sourceResult_preserved d 6 (by decide) (by decide) (by decide)).trans
      (h.clean 6 (by decide))
  have hb7 : b.stacks 7 = [] :=
    (SubexpJobFrames.sourceResult_preserved d 7 (by decide) (by decide) (by decide)).trans
      (h.clean 7 (by decide))
  obtain ⟨costs, n, e, he, hlength, hvisit, hs, hn⟩ :=
    UnaryGridProgram.grid_correct SubexpExtractionJobProgram.emitOne
      (step xs source width) (callbackCost xs source width) b
      (callback_spec b xs source width hb) (by simpa using hb.u) (by simpa using hb.z)
      hb6 hb7 hb.temporary
  rw [hbD] at hs hn
  have hbout : b.stacks 14 = d.stacks 14 :=
    SubexpJobFrames.sourceResult_preserved d 14 (by decide) (by decide) (by decide)
  rw [hbout] at hs
  have hcache : e.stacks 15 = Encoding.frame source := by
    rw [hs]
    simpa using hb.cached
  have hclear := UnaryGridProgram.clear_eval 15 e
  refine ⟨_, UnaryGridProgram.cleared 15 e, ?_, hprep.seq (he.seq hclear), ?_⟩
  · have hsourceCost := SubexpJobFrames.sourceCost_eq d (h.clean 10 (by decide))
      (h.clean 17 (by decide))
    rw [h.source] at hsourceCost
    have hgrid := hn.trans (gridCost_bound xs source D width)
    rw [hsourceCost, hcache, Encoding.length_frame]
    omega
  · funext i
    by_cases h15 : i = 15
    · subst i
      simp [UnaryGridProgram.cleared, h.clean 15 (by decide)]
    by_cases h14 : i = 14
    · subst i
      simp [UnaryGridProgram.cleared, hs]
    have hvalue : b.stacks i = d.stacks i := by
      by_cases h10 : i = 10
      · subst i
        exact hb.key.trans (h.clean 10 (by decide)).symm
      by_cases h17 : i = 17
      · subst i
        exact (SubexpJobFrames.sourceResult_clean d).2.trans (h.clean 17 (by decide)).symm
      exact SubexpJobFrames.sourceResult_preserved d i h10 h15 h17
    simpa [UnaryGridProgram.cleared, hs, h15, h14] using hvalue

def rowJobs (xs source : List Bool) (width z count : ℕ) : List Job :=
  (List.range count).map fun u => SubexpExtractionJobProgram.job xs source u z width

def gridJobs (xs source : List Bool) (D width count : ℕ) : List Job :=
  (List.range count).flatMap fun z => rowJobs xs source width z (D + 1)

theorem rowOutput_jobs (xs source : List Bool) (width z count : ℕ) (old : List Job) :
    UnaryGridProgram.rowOutput (step xs source width) z count (SubexpMomentProgram.input old) =
      SubexpMomentProgram.input ((rowJobs xs source width z count).reverse ++ old) := by
  induction count with
  | zero => simp [UnaryGridProgram.rowOutput, rowJobs]
  | succ count ih =>
    rw [UnaryGridProgram.rowOutput, ih]
    simp [step, rowJobs, List.range_succ,
      List.reverse_append, SubexpMomentProgram.input, Encoding.encodeList]

theorem gridOutput_jobs (xs source : List Bool) (D width count : ℕ) (old : List Job) :
    UnaryGridProgram.gridOutput (step xs source width) D count (SubexpMomentProgram.input old) =
      SubexpMomentProgram.input ((gridJobs xs source D width count).reverse ++ old) := by
  induction count with
  | zero => simp [UnaryGridProgram.gridOutput, gridJobs]
  | succ count ih =>
    rw [UnaryGridProgram.gridOutput, ih, rowOutput_jobs]
    simp [gridJobs, List.range_succ, List.flatMap_append, List.reverse_append,
      List.append_assoc]

theorem gridJobs_length (xs source : List Bool) (D width count : ℕ) :
    (gridJobs xs source D width count).length = count * (D + 1) := by
  simp [gridJobs, rowJobs, List.length_flatMap]

theorem gridJobs_eq_fixedKey {D : ℕ} (a : Fin D → ℕ) (source : List Bool)
    (ha : ∑ i, a i ≤ 2 * D + 1) :
    gridJobs (SymbolicCost.unaryWords (List.ofFn a)) source D
      (SubexpSymbolicCost.indexBits D) D =
      (List.range D).flatMap (fun z => (List.range (D + 1)).map fun u =>
        (⟨List.replicate z true, SubexpSymbolicCost.fixedKey (a, u, z), source⟩ : Job)) := by
  unfold gridJobs
  apply List.flatMap_congr
  intro z hz
  unfold rowJobs
  apply List.map_congr_left
  intro u hu
  exact SubexpExtractionJobProgram.job_eq_fixedKey a source u z
    ⟨ha, List.mem_range.mp hu, List.mem_range.mp hz⟩

/-- An actual fixed table creates the exact reversed U/Z job list, preserves
every input word, and restores all scratch words. -/
theorem program_runs (d : Data) (xs source : List Bool) (D width : ℕ) (old : List Job)
    (h : Input d xs source D width) (hout : d.stacks 14 = SubexpMomentProgram.input old) :
    ∃ e : Data, RunsIn program (gridCost xs source D width + 19 * source.length + 22)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 14
        (SubexpMomentProgram.input ((gridJobs xs source D width D).reverse ++ old)) := by
  obtain ⟨ticks, e, ht, he, hs⟩ := command_eval d xs source D width h
  rw [hout, gridOutput_jobs] at hs
  exact ⟨e, ⟨ticks + 1, by omega, StructuredCalls.compiled_halt_trace he 0 14⟩, hs⟩

end SubexponentialSAT.SubexpExtractionGrid

end OAI.Algorithms
