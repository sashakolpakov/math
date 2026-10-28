import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryRowProgram

namespace OAI.Algorithms

/-! A closed, actual interval enumerator for unary validity rows. -/

namespace SubexponentialSAT.SubexpUnaryRowEnumeration

open BitProgram StructuredCalls SubexpEnumerationProgram CounterPrograms
open SubexpUnaryRowProgram (Data Clean answer body body_eval)

def ports : SubexpEnumerationProgram.Ports 8 16 where
  register := ⟨fun i => i.castAdd 5, by
    intro i j h
    exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h)⟩
  current := 10
  remaining := 11
  scratch := 12
  current_ne_remaining := by decide
  current_ne_scratch := by decide
  remaining_ne_scratch := by decide

def rows (width start count : ℕ) : List Bool :=
  (List.range' start count).reverse.map (answer width)

theorem rows_succ (width start count : ℕ) :
    rows width start (count + 1) = answer width (start + count) :: rows width start count := by
  simp [rows, List.range'_1_concat, List.reverse_append]

@[simp] theorem rows_length (width start count : ℕ) : (rows width start count).length = count := by
  simp [rows]

def bodyBound (modulus : List Bool) : ℕ := 38 * modulus.length + 45

structure Invariant (modulus width initialOutput : List Bool) (start count : ℕ) (d : Data) : Prop where
  modulus_eq : d.stacks 13 = modulus
  width_eq : d.stacks 14 = width
  clean : Clean d.stacks
  rank_width : (d.stacks 10).length ≤ modulus.length
  fuel_width : (d.stacks 11).length ≤ modulus.length
  progress : ∃ done, done ≤ count ∧ value (d.stacks 10) = start + done ∧
    value (d.stacks 11) = count - done ∧ d.stacks 15 = rows width.length start done ++ initialOutput

private theorem invariant_stacks {modulus width output : List Bool} {start count : ℕ}
    {a b : Data} (h : a.stacks = b.stacks) (ha : Invariant modulus width output start count a) :
    Invariant modulus width output start count b := by
  rcases ha with ⟨hp, hw, hc, hr, hf, hprogress⟩
  constructor
  · simpa only [← h] using hp
  · simpa only [← h] using hw
  · simpa only [← h] using hc
  · simpa only [← h] using hr
  · simpa only [← h] using hf
  · simpa only [← h] using hprogress

private theorem next_frame (d : Data) (i : Fin 16)
    (h10 : i ≠ 10) (h11 : i ≠ 11) (h12 : i ≠ 12) :
    (nextState ports d).stacks i = d.stacks i :=
  nextState_other_stack ports d i h10 h11 h12

theorem body_step (modulus width output : List Bool) (start count : ℕ)
    (hwidth : width.length ≤ modulus.length) (hlimit : start + count < 2 ^ modulus.length) :
    SubexpEnumerationSchedule.BodyStep ports body
      (Invariant modulus width output start count) (fun _ => bodyBound modulus) := by
  intro d hd hs hp hf
  have hp' : 0 < value (d.stacks 11) := hp
  obtain ⟨done, hdone, hcur, hrem, hout⟩ := hd.progress
  obtain ⟨rf, he⟩ := body_eval (d.stacks 10) modulus width d.regs d.stacks
    hd.clean rfl hd.modulus_eq hd.width_eq hd.rank_width hwidth
  let e : Data := ⟨rf, Function.update d.stacks 15
    (answer width.length (value (d.stacks 10)) :: d.stacks 15)⟩
  have he10 : e.stacks 10 = d.stacks 10 := by simp [e]
  have he11 : e.stacks 11 = d.stacks 11 := by simp [e]
  have he12 : e.stacks 12 = [] := by simpa [e, ports] using hs
  have hncur : value ((nextState ports e).stacks 10) = start + (done + 1) := by
    change value ((nextState ports e).stacks ports.current) = _
    rw [nextState_current, value_increment]
    simp only [ports, he10, hcur]
    omega
  have hnrem : value ((nextState ports e).stacks 11) = count - (done + 1) := by
    change value ((nextState ports e).stacks ports.remaining) = _
    rw [nextState_remaining]
    have hdec := value_decrement (bs := e.stacks ports.remaining)
      (by simpa only [ports, he11] using hp')
    change value (ripple false (e.stacks 11)) + 1 = value (e.stacks 11) at hdec
    change value (ripple false (e.stacks 11)) = _
    rw [he11] at hdec ⊢
    rw [hrem] at hdec
    omega
  have hi : Invariant modulus width output start count (nextState ports e) := by
    constructor
    · rw [next_frame e 13 (by decide) (by decide) (by decide)]
      simpa [e] using hd.modulus_eq
    · rw [next_frame e 14 (by decide) (by decide) (by decide)]
      simpa [e] using hd.width_eq
    · intro i
      have h10 : i.castAdd 6 ≠ (10 : Fin 16) := by
        intro h; have hv := congrArg Fin.val h; change i.val = 10 at hv; omega
      have h11 : i.castAdd 6 ≠ (11 : Fin 16) := by
        intro h; have hv := congrArg Fin.val h; change i.val = 11 at hv; omega
      have h12 : i.castAdd 6 ≠ (12 : Fin 16) := by
        intro h; have hv := congrArg Fin.val h; change i.val = 12 at hv; omega
      have h15 : i.castAdd 6 ≠ (15 : Fin 16) := by
        intro h; have hv := congrArg Fin.val h; change i.val = 15 at hv; omega
      rw [next_frame e _ h10 h11 h12]
      simpa [e, h15] using hd.clean i
    · change ((nextState ports e).stacks ports.current).length ≤ _
      rw [nextState_current]
      change (ripple true (e.stacks 10)).length ≤ _
      rw [he10]
      apply increment_length_le_of_lt _ _ hd.rank_width
      rw [hcur]
      omega
    · change ((nextState ports e).stacks ports.remaining).length ≤ _
      rw [nextState_remaining]
      have hep : 0 < value (e.stacks 11) := by simpa only [he11] using hp'
      change (ripple false (e.stacks 11)).length ≤ modulus.length
      rw [decrement_length hep, he11]
      exact hd.fuel_width
    · refine ⟨done + 1, by omega, hncur, hnrem, ?_⟩
      rw [next_frame e 15 (by decide) (by decide) (by decide)]
      simp [e, hcur, hout, rows_succ]
  refine ⟨_, e, he, he10, he11, he12, hi, ?_⟩
  dsimp [bodyBound]
  have hr := hd.rank_width
  omega

def program := SubexpEnumerationProgram.program ports body

theorem program_runs (modulus width : List Bool) (d : Data)
    (hmodulus : d.stacks 13 = modulus) (hwidth : d.stacks 14 = width)
    (hc : Clean d.stacks) (hs : d.stacks 12 = [])
    (hrank : (d.stacks 10).length ≤ modulus.length)
    (hfuel : (d.stacks 11).length ≤ modulus.length)
    (hwidthLen : width.length ≤ modulus.length)
    (hlimit : value (d.stacks 10) + value (d.stacks 11) < 2 ^ modulus.length) :
    ∃ e : Data,
      RunsIn program (SubexpEnumerationSchedule.programBudget ports (fun _ => bodyBound modulus) d)
        (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 15 = rows width.length (value (d.stacks 10)) (value (d.stacks 11)) ++ d.stacks 15 ∧
      e.stacks 13 = modulus ∧ e.stacks 14 = width ∧ Clean e.stacks ∧
      (e.stacks 10).length ≤ modulus.length ∧ (e.stacks 11).length ≤ modulus.length ∧
      e.stacks 12 = [] ∧ value (e.stacks 11) = 0 := by
  let start := value (d.stacks 10)
  let count := value (d.stacks 11)
  have hi : Invariant modulus width (d.stacks 15) start count d := by
    refine ⟨hmodulus, hwidth, hc, hrank, hfuel, 0, Nat.zero_le _, ?_, ?_, ?_⟩ <;>
      simp [start, count, rows]
  have ht : Invariant modulus width (d.stacks 15) start count (testResult ports d) :=
    invariant_stacks (testResult_stacks ports d hs).symm hi
  obtain ⟨e, he, hr, _, hrem, hscratch⟩ := SubexpEnumerationSchedule.program_runsIn
    ports body (Invariant modulus width (d.stacks 15) start count) (fun _ => bodyBound modulus)
    (body_step modulus width (d.stacks 15) start count hwidthLen hlimit) d ht hs
  obtain ⟨done, hdone, _, hdrem, hdout⟩ := he.progress
  have hdoneEq : done = count := by
    change value (e.stacks 11) = 0 at hrem
    omega
  exact ⟨e, hr, by simpa only [hdoneEq] using hdout,
    he.modulus_eq, he.width_eq, he.clean, he.rank_width, he.fuel_width, hscratch, hrem⟩

end SubexponentialSAT.SubexpUnaryRowEnumeration

end OAI.Algorithms
