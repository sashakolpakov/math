import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisColorLoop

namespace OAI.Algorithms

/-! The concrete global-basis source program, from its retained input words
to the outer-first matrix bundle. No global matrix or read plan is an input. -/

namespace SubexponentialSAT.Subexp.GlobalBasisProgram

open BitProgram StructuredCalls
open GlobalBasisInput (Context Location)

theorem sequence_append {first second : List Code} {a b c : Data} {n m : ℕ}
    (hfirst : Eval (sequence first) n a b) (hsecond : Eval (sequence second) m b c) :
    Eval (sequence (first ++ second)) (n+m) a c := by
  induction first generalizing a n with
  | nil =>
    cases hfirst with
    | base h =>
      cases h
      simpa [sequence] using hsecond
  | cons code rest ih =>
    cases hfirst with
    | seq hc hr =>
      simpa only [List.cons_append, sequence, List.foldr, Nat.add_assoc] using hc.seq (ih hr)

structure Inputs {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ))
    (before : List (List Bool)) (tail : List Bool) (d : Data) : Prop where
  width : d.stacks 13 = List.replicate (GlobalBasisEntry.frameWidth p) true
  zero : d.stacks 14 = GlobalBasisEntry.scalarFrame p 0
  one : d.stacks 15 = GlobalBasisEntry.scalarFrame p 1
  position : d.stacks 32 = List.replicate C.position.val true
  metadata : d.stacks 33 = SelectorProgram.rawRecords C.metadata
  universal : d.stacks 37 = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)
  colors : d.stacks 38 = List.replicate r true
  group : d.stacks 47 = GlobalBasisRecordLookup.recordsPrefix before ++
    GlobalBasisRecordLookup.record C.batch ++ tail
  groupIndex : before.length = C.position.val
  dimension : d.stacks 46 = List.replicate locs.length true
  blocks : d.stacks 48 = List.replicate count true
  leftovers : d.stacks 49 = List.replicate leftovers true
  work : WorkClean d
  groupEmpty : d.stacks 40 = []
  counterEmpty : d.stacks 55 = []
  outputEmpty : d.stacks 63 = []

def bundleBits {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ)) : List Bool :=
  outerRecord C count leftovers locs ++ innerPrefix C count locs r ++ [false]

def innerPayloadAt {p r Q Δ : ℕ} (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) (g : ℕ) : List Bool :=
  if hg : g < r then
    GlobalBasisMatrixOutput.payload (List.replicate (innerColumns C count ⟨g,hg⟩).length true)
      (matrixBits C locs (innerColumns C count ⟨g,hg⟩))
  else []

def bundlePayloads {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ)) : List (List Bool) :=
  GlobalBasisMatrixOutput.payload (List.replicate (outerColumnsList C count leftovers).length true)
    (matrixBits C locs (outerColumnsList C count leftovers)) ::
      (List.range r).map (innerPayloadAt C count locs)

private theorem encoded_records (words : List (List Bool)) :
    Encoding.encodeList id words =
      words.flatMap (fun bits => true :: Encoding.frame bits) ++ [false] := by
  induction words with
  | nil => rfl
  | cons bits words ih => simp [Encoding.encodeList, ih, List.append_assoc]

theorem bundleBits_eq_records {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ)) :
    bundleBits C count leftovers locs = ProgramEncoding.encodeRecords (bundlePayloads C count leftovers locs) := by
  have hinner : innerPrefix C count locs r =
      (List.range r).flatMap (fun g => true :: Encoding.frame (innerPayloadAt C count locs g)) := by
    apply List.flatMap_congr
    intro g hg
    have hgr := List.mem_range.mp hg
    simp [innerWordAt, innerPayloadAt, hgr, innerRecord, GlobalBasisMatrixOutput.record]
  simp [bundleBits, hinner, ProgramEncoding.encodeRecords, bundlePayloads,
    encoded_records, List.flatMap_map, outerRecord, GlobalBasisMatrixOutput.record, List.append_assoc]

def totalBudget {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ)) (sourceLength : ℕ) : ℕ :=
  2 + 30 * (sourceLength + C.position.val + 1) + (7*r+5) +
    colorBudget C count locs r + outerPhaseBudget C count leftovers locs + (2*C.batch.length+3)

theorem command_eval {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ))
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : Inputs C count leftovers locs before tail d)
    (hm : C.locations 0 locs)
    (hinner : ∀ g : Fin r, ∀ loc ∈ locs, ∀ x ∈ innerColumns C count g, GlobalBasisEntry.Valid (C.row loc) x)
    (houter : ∀ loc ∈ locs, ∀ x ∈ outerColumnsList C count leftovers, GlobalBasisEntry.Valid (C.row loc) x) :
    ∃ n e, n ≤ totalBudget C count leftovers locs (d.stacks 47).length ∧
      Eval command n d e ∧
      e.stacks = Function.update d.stacks 63 (bundleBits C count leftovers locs) := by
  let a := TupleProgram.pushedState 63 0 false d
  have ha := push_eval 63 false d
  obtain ⟨n₁, b, hn₁, hb, hsb⟩ := getGroup_eval before C.batch tail a
    (by simpa [a, TupleProgram.pushedState] using H.group)
    (by simpa [a, TupleProgram.pushedState, H.groupIndex, GlobalBasisRecordLookup.unary] using H.position)
    (by simp [a, H.groupEmpty])
    (by simp [a, H.work 16 (by decide)])
    (by simp [a, H.work 17 (by decide)])
    (by simp [a, H.work 18 (by decide)])
    (by simp [a, H.work 19 (by decide)])
  let c := copied 38 55 b
  have hc := copy_eval 38 55 b (by decide) (by decide) (by decide)
    (by simp [hsb, a, H.work 31 (by decide)])
  have hcs : c.stacks = Function.update (Function.update (Function.update d.stacks
      63 [false]) 40 C.batch) 55 (List.replicate r true) := by
    simp [c, copied, StackRoutines.copyStacks, hsb, a,
      H.colors, H.counterEmpty, H.outputEmpty]
  have hcstored : C.Stored c := by
    constructor
    · simpa [hcs] using H.width
    · simpa [hcs] using H.zero
    · simpa [hcs] using H.one
    · simpa [hcs] using H.position
    · simpa [hcs] using H.metadata
    · simpa [hcs] using H.universal
    · simpa [hcs] using H.colors
    · simp [hcs]
  have hcclean : WorkClean c := by
    intro i hi
    have hi40 : i ≠ 40 := by intro he; subst i; exact hi (by decide)
    have hi55 : i ≠ 55 := by intro he; subst i; exact hi (by decide)
    have hi63 : i ≠ 63 := by intro he; subst i; exact hi (by decide)
    simpa [hcs, hi40, hi55, hi63] using H.work i hi
  obtain ⟨n₂, f, hn₂, hf, hsf⟩ := innerMatrices_eval C count locs c hm hcstored hcclean
    (by simp [hcs, H.dimension]) (by simp [hcs, H.blocks]) (by simp [hcs]) hinner
  obtain ⟨n₃, g, hn₃, hg, hsg⟩ := outerPhase_eval C count leftovers locs f hm
    (stored_color_frame hcstored _ _ hsf) (clean_color_frame hcclean _ _ hsf)
    (by simp [hsf, hcs, H.dimension]) (by simp [hsf, hcs, H.blocks])
    (by simp [hsf, hcs, H.leftovers]) houter
  let e := cleared 40 g
  have hclear : Eval (sequence [clear 40]) (2 * (g.stacks 40).length + 3) g e := by
    simpa only [sequence, List.foldr, Nat.add_zero] using
      (clear_eval 40 g).seq (.base (.skip e))
  have hlast := sequence_append hg hclear
  have hall := ha.seq (hb.seq (hc.seq (hf.seq hlast)))
  have hb38 : (b.stacks 38).length = r := by simp [hsb, a, H.colors]
  have hg40 : (g.stacks 40).length = C.batch.length := by simp [hsg, hsf, hcs]
  have ha47 : (a.stacks 47).length = (d.stacks 47).length := by simp [a]
  have ha32 : (a.stacks 32).length = C.position.val := by simp [a, H.position]
  rw [hb38, hg40] at hall
  rw [ha47, ha32] at hn₁
  refine ⟨_, e, ?_, by simpa only [command, sequence, List.foldr, List.cons_append, List.nil_append] using hall, ?_⟩
  · unfold totalBudget
    omega
  · funext i
    by_cases hi40 : i = 40
    · subst i; simp [e, cleared, H.groupEmpty]
    by_cases hi55 : i = 55
    · subst i; simp [e, cleared, hsg, hsf, hcs, H.counterEmpty]
    by_cases hi63 : i = 63
    · subst i; simp [e, cleared, hsg, hsf, hcs, bundleBits, List.append_assoc]
    · simp [e, cleared, hsg, hsf, hcs, hi40, hi55, hi63]

theorem program_runsIn {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ))
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : Inputs C count leftovers locs before tail d) (hm : C.locations 0 locs)
    (hinner : ∀ g : Fin r, ∀ loc ∈ locs, ∀ x ∈ innerColumns C count g, GlobalBasisEntry.Valid (C.row loc) x)
    (houter : ∀ loc ∈ locs, ∀ x ∈ outerColumnsList C count leftovers, GlobalBasisEntry.Valid (C.row loc) x) :
    ∃ e : Data, RunsIn program (totalBudget C count leftovers locs (d.stacks 47).length + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 63 (bundleBits C count leftovers locs) := by
  obtain ⟨n, e, hn, he, hs⟩ := command_eval C count leftovers locs before tail d H hm hinner houter
  exact ⟨e, ⟨n+1, by omega, compiled_halt_trace he 47 63⟩, hs⟩

theorem program_runsIn_records {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ))
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : Inputs C count leftovers locs before tail d) (hm : C.locations 0 locs)
    (hinner : ∀ g : Fin r, ∀ loc ∈ locs, ∀ x ∈ innerColumns C count g, GlobalBasisEntry.Valid (C.row loc) x)
    (houter : ∀ loc ∈ locs, ∀ x ∈ outerColumnsList C count leftovers, GlobalBasisEntry.Valid (C.row loc) x) :
    ∃ e : Data, RunsIn program (totalBudget C count leftovers locs (d.stacks 47).length + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 63 (ProgramEncoding.encodeRecords (bundlePayloads C count leftovers locs)) := by
  simpa only [bundleBits_eq_records] using program_runsIn C count leftovers locs before tail d H hm hinner houter

end SubexponentialSAT.Subexp.GlobalBasisProgram

end OAI.Algorithms
