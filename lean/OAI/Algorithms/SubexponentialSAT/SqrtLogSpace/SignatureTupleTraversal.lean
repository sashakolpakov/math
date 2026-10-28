import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsBuckets
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Cursor semantics for the attained-signature tuple controller

The cursor stores an attained prefix and one numeric candidate. Suspended
ancestors are first occurrences, so the tree branches over attained keys only.
The traces and finite sums below are mathematical specifications; the actual
controller retains neither a trace nor a family of assignments or tuples.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

open scoped BigOperators
open SignatureTupleDFS

open Classical

variable {N : ℕ → ℕ} {κ : ℕ → Type*}

abbrev Representatives (key : (d : ℕ) → Fin (N d) → κ d) (d : ℕ) :=
  AttainedSignatures.Representative (key d)

/-- The finite prefix specifies the suspended candidate frames,
in root-to-current order. Exhaustion is represented by `candidate = N depth`. -/
inductive Cursor (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
  | scan (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val)
      (candidate : ℕ)
  | leaf (ancestors : Prefix (Representatives key) levels)
  | halt

/-- Every probe, including a losing one, every exhausted generator, and every
leaf callback has its own event. None of these domains is stored at runtime. -/
inductive Event (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
  | candidate (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val)
      (candidate : Fin (N depth.val))
  | exhausted (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val)
  | leaf (ancestors : Prefix (Representatives key) levels)

def enter (key : (d : ℕ) → Fin (N d) → κ d) (levels depth : ℕ)
    (hd : depth ≤ levels) (ancestors : Prefix (Representatives key) depth) : Cursor key levels :=
  if h : depth = levels then .leaf (h ▸ ancestors)
  else .scan ⟨depth, lt_of_le_of_ne hd h⟩ ancestors 0

def leave (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ) :
    (depth : ℕ) → depth ≤ levels → Prefix (Representatives key) depth → Cursor key levels
  | 0, _, _ => .halt
  | depth + 1, hd, ancestors => .scan ⟨depth, by omega⟩ (Fin.init ancestors)
      ((ancestors (Fin.last depth)).val.val + 1)

@[simp] theorem enter_internal (key : (d : ℕ) → Fin (N d) → κ d)
    (levels depth : ℕ) (hd : depth < levels) (ancestors : Prefix (Representatives key) depth) :
    enter key levels depth hd.le ancestors = .scan ⟨depth, hd⟩ ancestors 0 := by
  simp [enter, Nat.ne_of_lt hd]

@[simp] theorem enter_leaf (key : (d : ℕ) → Fin (N d) → κ d)
    (levels : ℕ) (ancestors : Prefix (Representatives key) levels) :
    enter key levels levels le_rfl ancestors = .leaf ancestors := by simp [enter]

@[simp] theorem leave_snoc (key : (d : ℕ) → Fin (N d) → κ d)
    (levels depth : ℕ) (hd : depth < levels) (ancestors : Prefix (Representatives key) depth)
    (rep : Representatives key depth) :
    leave key levels (depth + 1) hd (Fin.snoc ancestors rep) =
      .scan ⟨depth, hd⟩ ancestors (rep.val.val + 1) := by
  simp [leave]

/-- These are exactly the four controller branches, including advancement
only after a child has returned. Root exhaustion alone halts the cursor. -/
inductive Step (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ) :
    Event key levels → Cursor key levels → Cursor key levels → Prop
  | fresh (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val)
      (rep : Representatives key depth.val) :
      Step key levels (.candidate depth ancestors rep.val)
        (.scan depth ancestors rep.val.val)
        (enter key levels (depth.val + 1) depth.isLt (Fin.snoc ancestors rep))
  | duplicate (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val)
      (candidate : Fin (N depth.val))
      (hd : ¬ ∀ j, j < candidate → key depth.val j ≠ key depth.val candidate) :
      Step key levels (.candidate depth ancestors candidate)
        (.scan depth ancestors candidate.val) (.scan depth ancestors (candidate.val + 1))
  | exhausted (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val) :
      Step key levels (.exhausted depth ancestors) (.scan depth ancestors (N depth.val))
        (leave key levels depth.val depth.isLt.le ancestors)
  | leaf (ancestors : Prefix (Representatives key) levels) :
      Step key levels (.leaf ancestors) (.leaf ancestors) (leave key levels levels le_rfl ancestors)

/-- A proof-level weighted trace. Taking indicator weights states exact
visit counts; taking natural costs charges actual source evaluations. -/
inductive Trace {key : (d : ℕ) → Fin (N d) → κ d} {levels : ℕ}
    {M : Type*} [AddMonoid M] (weight : Event key levels → M) :
    M → Cursor key levels → Cursor key levels → Prop
  | refl (a) : Trace weight 0 a a
  | step {event a b c total} : Step key levels event a b → Trace weight total b c →
      Trace weight (weight event + total) a c

theorem Trace.single {key : (d : ℕ) → Fin (N d) → κ d} {levels : ℕ}
    {M : Type*} [AddMonoid M] (weight : Event key levels → M)
    {event a b} (h : Step key levels event a b) : Trace weight (weight event) a b := by
  simpa using Trace.step h (.refl b : Trace weight 0 b b)

theorem Trace.trans {key : (d : ℕ) → Fin (N d) → κ d} {levels : ℕ}
    {M : Type*} [AddMonoid M] {weight : Event key levels → M}
    {a b c x y} (h : Trace weight x a b) (h' : Trace weight y b c) :
    Trace weight (x + y) a c := by
  induction h with
  | refl => simpa using h'
  | step hs _ ih => simpa only [add_assoc] using Trace.step hs (ih h')

private theorem sum_tail_succ {M : Type*} [AddCommMonoid M] {n : ℕ}
    (f : Fin n → M) (c : Fin n) :
    (∑ i : Fin n with c.val ≤ i.val, f i) =
      f c + ∑ i : Fin n with c.val + 1 ≤ i.val, f i := by
  classical
  have hs : (Finset.univ.filter fun i : Fin n => c.val ≤ i.val) =
      insert c (Finset.univ.filter fun i : Fin n => c.val + 1 ≤ i.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases he : i = c
      · exact Or.inl he
      · exact Or.inr (by have hn : i.val ≠ c.val := fun h => he (Fin.ext h); omega)
    · rintro (rfl | h) <;> omega
  rw [hs, Finset.sum_insert (by simp)]

/-- Weighted subtree size. The recursive sum is over first occurrences only;
the separate candidate sum charges every successful and losing probe. -/
noncomputable def subtreeTotal (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M) :
    (remaining depth : ℕ) → depth + remaining = levels →
      Prefix (Representatives key) depth → M := by
  classical
  intro remaining
  induction remaining with
  | zero =>
      intro depth h ancestors
      have he : depth = levels := by omega
      exact weight (.leaf (he ▸ ancestors))
  | succ remaining ih =>
      intro depth h ancestors
      let d : Fin levels := ⟨depth, by omega⟩
      exact (∑ i : Fin (N depth), weight (.candidate d ancestors i)) +
        weight (.exhausted d ancestors) +
        ∑ rep : Representatives key depth, ih (depth + 1) (by omega) (Fin.snoc ancestors rep)

private theorem sum_representatives {M : Type*} [AddCommMonoid M]
    (key : (d : ℕ) → Fin (N d) → κ d) (depth : ℕ)
    (f : Representatives key depth → M) :
    (∑ i : Fin (N depth),
      if h : ∀ j, j < i → key depth j ≠ key depth i then f ⟨i, h⟩ else 0) =
      ∑ rep : Representatives key depth, f rep := by
  classical
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro i hi
    split_ifs with h
    · exact (hi ⟨⟨i, h⟩, rfl⟩).elim
    · rfl
  · intro i
    rw [dite_eq_left i.property]

/-- A complete subtree starts at its first candidate and returns to the
parent's next candidate. This includes the terminal exhaustion test. -/
theorem subtree_trace (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M)
    (remaining depth : ℕ) (h : depth + remaining = levels)
    (ancestors : Prefix (Representatives key) depth) :
    Trace weight (subtreeTotal key levels weight remaining depth h ancestors)
      (enter key levels depth (by omega) ancestors)
      (leave key levels depth (by omega) ancestors) := by
  classical
  induction remaining generalizing depth with
  | zero =>
      have he : depth = levels := by omega
      subst depth
      simpa [subtreeTotal] using Trace.single weight (Step.leaf ancestors)
  | succ remaining ih =>
      let d : Fin levels := ⟨depth, by omega⟩
      let child : Representatives key depth → M := fun rep =>
        subtreeTotal key levels weight remaining (depth + 1) (by omega) (Fin.snoc ancestors rep)
      let charge : Fin (N depth) → M := fun i => weight (.candidate d ancestors i) +
        if hi : ∀ j, j < i → key depth j ≠ key depth i then child ⟨i, hi⟩ else 0
      have scan : ∀ left c, c + left = N depth →
          Trace weight ((∑ i : Fin (N depth) with c ≤ i.val, charge i) +
            weight (.exhausted d ancestors))
            (.scan d ancestors c) (leave key levels depth (by omega) ancestors) := by
        intro left
        induction left with
        | zero =>
            intro c hc
            have he : c = N depth := by omega
            subst c
            have hs : (∑ i : Fin (N depth) with N depth ≤ i.val, charge i) = 0 := by
              apply Finset.sum_eq_zero
              intro i hi
              have hn := (Finset.mem_filter.mp hi).2
              omega
            rw [hs, zero_add]
            exact Trace.single weight (.exhausted d ancestors)
        | succ left ihscan =>
            intro c hc
            let i : Fin (N depth) := ⟨c, by omega⟩
            have hn := ihscan (c + 1) (by omega)
            rw [show c = i.val from rfl, sum_tail_succ charge i]
            by_cases hf : ∀ j, j < i → key depth j ≠ key depth i
            · let rep : Representatives key depth := ⟨i, hf⟩
              have ht := ih (depth + 1) (by omega) (Fin.snoc ancestors rep)
              rw [leave_snoc key levels depth d.isLt ancestors rep] at ht
              have hh := (Trace.single weight (Step.fresh d ancestors rep)).trans (ht.trans hn)
              simpa only [charge, dite_eq_left hf, child, add_assoc] using hh
            · have hh := (Trace.single weight (Step.duplicate d ancestors i hf)).trans hn
              simpa only [charge, dite_eq_right hf, add_zero, add_assoc] using hh
      have hs := scan (N depth) 0 (by omega)
      simp only [Nat.zero_le, Finset.filter_true, charge, Finset.sum_add_distrib] at hs
      rw [sum_representatives] at hs
      rw [enter_internal key levels depth d.isLt ancestors]
      change Trace weight
        (((∑ i : Fin (N depth), weight (.candidate d ancestors i)) +
          weight (.exhausted d ancestors)) + ∑ rep, child rep)
        (.scan d ancestors 0) _
      rw [add_right_comm] at hs
      exact hs

/-- The exact charge of the invocation domain at one depth. -/
noncomputable def levelTotal (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M) (depth : ℕ) : M :=
  if hd : depth < levels then
    ∑ ancestors : Prefix (Representatives key) depth,
      ((∑ i : Fin (N depth), weight (.candidate ⟨depth, hd⟩ ancestors i)) +
        weight (.exhausted ⟨depth, hd⟩ ancestors))
  else 0

/-- Sum over every internal attained prefix and every complete attained tuple.
Each candidate and exhaustion appears once per internal invocation. -/
noncomputable def eventTotal (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M) : M :=
  (∑ depth ∈ Finset.range levels, levelTotal key levels weight depth) +
    ∑ ancestors : Prefix (Representatives key) levels, weight (.leaf ancestors)

private theorem sum_snoc {M : Type*} [AddCommMonoid M]
    (key : (d : ℕ) → Fin (N d) → κ d) (depth : ℕ)
    (f : Prefix (Representatives key) (depth + 1) → M) :
    (∑ ancestors : Prefix (Representatives key) depth,
      ∑ rep : Representatives key depth, f (Fin.snoc ancestors rep)) = ∑ ancestors, f ancestors := by
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact (Fin.snocEquiv (fun i : Fin (depth + 1) => Representatives key i.val)).sum_comp f

private theorem sum_subtreeTotal (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M)
    (remaining depth : ℕ) (h : depth + remaining = levels) :
    (∑ ancestors : Prefix (Representatives key) depth,
      subtreeTotal key levels weight remaining depth h ancestors) =
        (∑ d ∈ Finset.Ico depth levels, levelTotal key levels weight d) +
          ∑ ancestors : Prefix (Representatives key) levels, weight (.leaf ancestors) := by
  induction remaining generalizing depth with
  | zero =>
      have he : depth = levels := by omega
      subst depth
      simp [subtreeTotal]
  | succ remaining ih =>
      have hd : depth < levels := by omega
      change (∑ ancestors : Prefix (Representatives key) depth,
        (((∑ i : Fin (N depth), weight (.candidate ⟨depth, hd⟩ ancestors i)) +
          weight (.exhausted ⟨depth, hd⟩ ancestors)) +
        ∑ rep : Representatives key depth,
          subtreeTotal key levels weight remaining (depth + 1) (by omega)
            (Fin.snoc ancestors rep))) = _
      rw [Finset.sum_add_distrib, sum_snoc, ih (depth + 1) (by omega),
        Finset.sum_eq_sum_Ico_succ_bot hd]
      simp only [levelTotal, dite_eq_left hd]
      simp only [add_assoc]

/-- Every candidate, exhausted generator and leaf in the attained-prefix
domain is visited exactly once: this holds for arbitrary additive weights. -/
theorem complete_trace (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → M) :
    Trace weight (eventTotal key levels weight)
      (enter key levels 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) .halt := by
  have hs := sum_subtreeTotal key levels weight levels 0 (by omega)
  rw [Fintype.sum_subsingleton _ (fun i => Fin.elim0 i)] at hs
  have ht := subtree_trace key levels weight levels 0 (by omega) (fun i => Fin.elim0 i)
  simpa only [hs, ← Finset.range_eq_Ico, eventTotal, leave] using ht

/-- Weighted native iterations before the final loop-guard test. This is a
proof relation over actual evaluations, not an executable trace container. -/
inductive Iterations {r s : ℕ} (p : SignatureTupleProgram.Ports r)
    (q : SignatureTupleProgram.Routines r s) :
    ℕ → StructuredProgram.State r s → StructuredProgram.State r s → Prop
  | refl (a) : Iterations p q 0 a a
  | step {a b c n m} : a.regs p.active = true →
      SignatureTupleProgram.Iteration p q n a b → Iterations p q m b c →
      Iterations p q (n + m + 1) a c

theorem Iterations.finish {r s : ℕ} {p : SignatureTupleProgram.Ports r}
    {q : SignatureTupleProgram.Routines r s} {n a b}
    (ht : Iterations p q n a b) (hb : b.regs p.active = false) :
    SignatureTupleProgram.Traversal p q (n + 1) a b := by
  induction ht with
  | refl => exact .done hb
  | step ha hi _ ih =>
      simpa only [Nat.add_assoc] using SignatureTupleProgram.Traversal.step ha hi (ih hb)

/-- Transfer the complete semantic path to actual controller iterations.
The same evaluations carry both the time charge and the callback accumulator.
Concrete routines must prove the local `hstep` clause. -/
theorem Trace.nativeIterations {key : (d : ℕ) → Fin (N d) → κ d} {levels : ℕ}
    {M : Type*} [AddCommMonoid M] {weight : Event key levels → ℕ × M}
    {total start finish} (ht : Trace weight total start finish)
    {r s : ℕ} (p : SignatureTupleProgram.Ports r) (q : SignatureTupleProgram.Routines r s)
    (Rel : Cursor key levels → M → StructuredProgram.State r s → Prop)
    (hstep : ∀ event before after acc a, Step key levels event before after → Rel before acc a →
      a.regs p.active = true ∧ ∃ n b, SignatureTupleProgram.Iteration p q n a b ∧
        Rel after (acc + (weight event).2) b ∧ n + 1 ≤ (weight event).1)
    (acc : M) (a : StructuredProgram.State r s) (ha : Rel start acc a) :
    ∃ n b, Iterations p q n a b ∧ Rel finish (acc + total.2) b ∧ n ≤ total.1 := by
  induction ht generalizing acc a with
  | refl => exact ⟨0, a, .refl a, by simpa using ha, by simp⟩
  | @step event before middle after tail hs _ ih =>
      obtain ⟨ha', n, b, hi, hb, hn⟩ := hstep event before middle acc a hs ha
      obtain ⟨m, c, hc, hrel, hm⟩ := ih (acc + (weight event).2) b hb
      refine ⟨n + m + 1, c, .step ha' hi hc, ?_, ?_⟩
      · simpa only [Prod.snd_add, add_assoc] using hrel
      · change n + m + 1 ≤ (weight event).1 + tail.1
        omega

/-- One actual controller traversal realizes the full weighted event sum.
The bound includes its final guard test; setup and compilation are charged by
`SignatureTupleProgram.program_trace` when this traversal is embedded. -/
theorem native_complete (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (weight : Event key levels → ℕ × M)
    {r s : ℕ} (p : SignatureTupleProgram.Ports r) (q : SignatureTupleProgram.Routines r s)
    (Rel : Cursor key levels → M → StructuredProgram.State r s → Prop)
    (hstep : ∀ event before after acc a, Step key levels event before after → Rel before acc a →
      a.regs p.active = true ∧ ∃ n b, SignatureTupleProgram.Iteration p q n a b ∧
        Rel after (acc + (weight event).2) b ∧ n + 1 ≤ (weight event).1)
    (hhalt : ∀ acc a, Rel .halt acc a → a.regs p.active = false)
    (acc : M) (a : StructuredProgram.State r s)
    (ha : Rel (enter key levels 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) acc a) :
    ∃ n b, SignatureTupleProgram.Traversal p q n a b ∧
      Rel .halt (acc + (eventTotal key levels weight).2) b ∧
      n ≤ (eventTotal key levels weight).1 + 1 := by
  obtain ⟨n, b, ht, hb, hn⟩ :=
    (complete_trace key levels weight).nativeIterations p q Rel hstep acc a ha
  exact ⟨n + 1, b, ht.finish (hhalt _ _ hb), hb, Nat.add_le_add_right hn 1⟩

/-- The exact invocation-domain bound, before any uniform polynomial
estimate. Full tuple callbacks are charged on the same event sum. -/
theorem eventTotal_le (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    (weight : Event key levels → ℕ) (cost : ℕ → ℕ) (leafCost : ℕ)
    (hc : ∀ (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val),
      (∑ i : Fin (N depth.val), weight (.candidate depth ancestors i)) +
        weight (.exhausted depth ancestors) ≤ cost depth.val)
    (hl : ∀ ancestors, weight (.leaf ancestors) ≤ leafCost) :
    eventTotal key levels weight ≤
      generatorWork (fun d => Fintype.card (Representatives key d)) cost levels +
        prefixCount (fun d => Fintype.card (Representatives key d)) levels * leafCost := by
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro depth hd
    have hd' : depth < levels := Finset.mem_range.mp hd
    simp only [levelTotal, dite_eq_left hd']
    calc
      _ ≤ ∑ _ancestors : Prefix (Representatives key) depth, cost depth :=
        Finset.sum_le_sum fun ancestors _ => hc ⟨depth, hd'⟩ ancestors
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
          card_prefix (Representatives key) depth]
  · calc
      _ ≤ ∑ _ancestors : Prefix (Representatives key) levels, leafCost :=
        Finset.sum_le_sum fun ancestors _ => hl ancestors
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
          card_prefix (Representatives key) levels]

/-- Per-candidate comparison charge; the index is a binary counter value,
not a retained word length. The rescan uses precisely its predecessors. -/
def costWeight (key : (d : ℕ) → Fin (N d) → κ d) (levels poly leafCost : ℕ) :
    Event key levels → ℕ
  | .candidate _ _ candidate => poly * (candidate.val + 1)
  | .exhausted _ _ => poly
  | .leaf _ => leafCost

theorem candidate_cost_le (n poly : ℕ) (hn : 1 ≤ n) :
    (∑ i : Fin n, poly * (i.val + 1)) + poly ≤ 2 * poly * (n * n) := by
  have hs : (∑ i : Fin n, poly * (i.val + 1)) ≤ n * (poly * n) := by
    calc
      _ ≤ ∑ _i : Fin n, poly * n :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left poly i.isLt
      _ = _ := by simp
  have hp : poly ≤ poly * (n * n) := Nat.le_mul_of_pos_right _ (by positivity)
  nlinarith

/-- The stronger runtime scale needs only one square of each head's raw
assignment count, multiplied by the attained-key product. -/
theorem eventTotal_cost_le (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels poly leafCost hmax : ℕ)
    (hh : ∀ d < levels, h d ≤ hmax) :
    eventTotal key levels (costWeight key levels poly leafCost) ≤
      (2 * poly) * levels *
        prefixCount (fun d => Fintype.card (Representatives key d)) levels * 4 ^ hmax +
      prefixCount (fun d => Fintype.card (Representatives key d)) levels * leafCost := by
  have hpos : ∀ d, 1 ≤ Fintype.card (Representatives key d) := by
    intro d
    have hp : 0 < Fintype.card (Representatives key d) := by
      simpa only [Nat.card_eq_fintype_card] using
        AttainedSignatures.card_representative_pos (key d) (pow_pos (by omega) _)
    omega
  have hc : ∀ (depth : Fin levels) (ancestors : Prefix (Representatives key) depth.val),
      (∑ i : Fin (2 ^ h depth.val),
        costWeight key levels poly leafCost (.candidate depth ancestors i)) +
      costWeight key levels poly leafCost (.exhausted depth ancestors) ≤
        (2 * poly) * 4 ^ h depth.val := by
    intro depth ancestors
    have he : 2 ^ h depth.val * 2 ^ h depth.val = 4 ^ h depth.val := by
      rw [← mul_pow]; rfl
    simpa only [costWeight, he] using candidate_cost_le (2 ^ h depth.val) poly
      (Nat.one_le_pow _ _ (by omega))
  exact (eventTotal_le key levels _ (fun d => (2 * poly) * 4 ^ h d) leafCost hc
    (fun _ => le_rfl)).trans (Nat.add_le_add_right
      (generatorWork_le_four_pow _ _ h levels (2 * poly) hmax
        (fun d _ => hpos d) (fun _ _ => le_rfl) hh) _)

/-- Only leaves alter the mathematical callback accumulator. -/
def callbackWeight (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [Zero M] (value : Prefix (Representatives key) levels → M) :
    Event key levels → M
  | .candidate _ _ _ => 0
  | .exhausted _ _ => 0
  | .leaf ancestors => value ancestors

theorem eventTotal_callbackWeight (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (value : Prefix (Representatives key) levels → M) :
    eventTotal key levels (callbackWeight key levels value) = ∑ ancestors, value ancestors := by
  simp [eventTotal, levelTotal, callbackWeight]

theorem eventTotal_map (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M A : Type*} [AddCommMonoid M] [AddCommMonoid A]
    (map : M →+ A) (weight : Event key levels → M) :
    eventTotal key levels (fun event => map (weight event)) =
      map (eventTotal key levels weight) := by
  unfold eventTotal
  rw [map_add, map_sum, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro depth _
  unfold levelTotal
  split_ifs <;> simp only [map_sum, map_add, map_zero]

/-- Cost and exact callback value share the same weighted traversal. -/
theorem eventTotal_pair (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (cost : Event key levels → ℕ)
    (value : Prefix (Representatives key) levels → M) :
    eventTotal key levels (fun event => (cost event, callbackWeight key levels value event)) =
      (eventTotal key levels cost, ∑ ancestors, value ancestors) := by
  apply Prod.ext
  · exact (eventTotal_map key levels (AddMonoidHom.fst ℕ M) _).symm
  · exact (eventTotal_map key levels (AddMonoidHom.snd ℕ M) _).symm.trans
      (eventTotal_callbackWeight key levels value)

/-- A concrete controller satisfying the local cursor invariant runs every
attained tuple callback once, with the squared-head cost on that same run.
This is the native integration lemma; its local clauses must be discharged
by the actual probe, frame, loader and callback commands. -/
theorem native_complete_bounded (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels poly leafCost hmax : ℕ)
    (hh : ∀ d < levels, h d ≤ hmax)
    {M : Type*} [AddCommMonoid M] (value : Prefix (Representatives key) levels → M)
    {r s : ℕ} (p : SignatureTupleProgram.Ports r) (q : SignatureTupleProgram.Routines r s)
    (Rel : Cursor key levels → M → StructuredProgram.State r s → Prop)
    (hstep : ∀ event before after acc a, Step key levels event before after → Rel before acc a →
      a.regs p.active = true ∧ ∃ n b, SignatureTupleProgram.Iteration p q n a b ∧
        Rel after (acc + callbackWeight key levels value event) b ∧
        n + 1 ≤ costWeight key levels poly leafCost event)
    (hhalt : ∀ acc a, Rel .halt acc a → a.regs p.active = false)
    (acc : M) (a : StructuredProgram.State r s)
    (ha : Rel (enter key levels 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) acc a) :
    ∃ n b, SignatureTupleProgram.Traversal p q n a b ∧
      Rel .halt (acc + ∑ ancestors, value ancestors) b ∧
      n ≤ (2 * poly) * levels *
        prefixCount (fun d => Fintype.card (Representatives key d)) levels * 4 ^ hmax +
        prefixCount (fun d => Fintype.card (Representatives key d)) levels * leafCost + 1 := by
  obtain ⟨n, b, ht, hb, hn⟩ := native_complete key levels
    (fun event => (costWeight key levels poly leafCost event,
      callbackWeight key levels value event)) p q Rel hstep hhalt acc a ha
  rw [eventTotal_pair] at hb hn
  refine ⟨n, b, ht, hb, hn.trans ?_⟩
  exact Nat.add_le_add_right (eventTotal_cost_le h key levels poly leafCost hmax hh) 1

section Frames

open ExecCNFTupleEnumeration SignatureTupleProgram

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- Exactly one bounded binary assignment word per retained ancestor. -/
def representativeWords (depth : ℕ) (ancestors : Prefix (Representatives key) depth) :
    List (List Bool) :=
  List.ofFn fun i : Fin depth => fixedBits (h i.val) (ancestors i).val.val

/-- The deepest ancestor is first on physical representative stack 837. -/
def representativeFrames (depth : ℕ) (ancestors : Prefix (Representatives key) depth) :
    List Bool := suspendedFrames (representativeWords h key depth ancestors).reverse

theorem representativeWords_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    representativeWords h key (depth + 1) (Fin.snoc ancestors rep) =
      representativeWords h key depth ancestors ++ [fixedBits (h depth) rep.val.val] := by
  simp only [representativeWords, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_last, List.concat_eq_append]
  rfl

theorem representativeFrames_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    representativeFrames h key (depth + 1) (Fin.snoc ancestors rep) =
      Encoding.frame (fixedBits (h depth) rep.val.val).reverse ++
        representativeFrames h key depth ancestors := by
  simp [representativeFrames, representativeWords_snoc, suspendedFrames, List.reverse_append]

/-- Popping an ancestor restores precisely the previous dependent prefix. -/
theorem representativeFrames_pop (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) :
    representativeFrames h key (depth + 1) ancestors =
      Encoding.frame (fixedBits (h depth) (ancestors (Fin.last depth)).val.val).reverse ++
        representativeFrames h key depth (Fin.init ancestors) := by
  simpa only [Fin.snoc_init_self] using
    representativeFrames_snoc h key depth (Fin.init ancestors) (ancestors (Fin.last depth))

/-- The frame order is the actual save-cursor command's order: remaining
first, then candidate. Both values use fixed polynomial word lengths. -/
def cursorFrame (width candidate : ℕ) : List Bool :=
  Encoding.frame (fixedBits (width + 1) (2 ^ width - candidate)).reverse ++
    Encoding.frame (fixedBits width candidate).reverse

def cursorFrames (depth : ℕ) (ancestors : Prefix (Representatives key) depth) : List Bool :=
  (List.ofFn fun i : Fin depth => cursorFrame (h i.val) (ancestors i).val.val).reverse.flatten

theorem cursorFrames_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    cursorFrames h key (depth + 1) (Fin.snoc ancestors rep) =
      cursorFrame (h depth) rep.val.val ++ cursorFrames h key depth ancestors := by
  simp only [cursorFrames, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_last, List.concat_eq_append,
    List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatten_cons]
  rfl

theorem cursorFrames_pop (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) :
    cursorFrames h key (depth + 1) ancestors =
      cursorFrame (h depth) (ancestors (Fin.last depth)).val.val ++
        cursorFrames h key depth (Fin.init ancestors) := by
  simpa only [Fin.snoc_init_self] using
    cursorFrames_snoc h key depth (Fin.init ancestors) (ancestors (Fin.last depth))

theorem representativeFrames_length_le (depth hmax : ℕ)
    (ancestors : Prefix (Representatives key) depth) (hh : ∀ d < depth, h d ≤ hmax) :
    (representativeFrames h key depth ancestors).length ≤ (2 * hmax + 1) * depth := by
  apply suspendedFrames_length_le _ hmax depth
  · simp [representativeWords]
  · intro word hw
    rw [List.mem_reverse, representativeWords, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    simpa using hh i.val i.isLt

private theorem flatten_length_le (words : List (List Bool)) (bound : ℕ)
    (hw : ∀ word ∈ words, word.length ≤ bound) : words.flatten.length ≤ words.length * bound := by
  induction words with
  | nil => simp
  | cons word words ih =>
      have hword := hw word (by simp)
      have htail := ih (fun w hmem => hw w (by simp [hmem]))
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem cursorFrame_length (width candidate : ℕ) :
    (cursorFrame width candidate).length = 4 * width + 4 := by
  simp [cursorFrame]
  omega

theorem cursorFrames_length_le (depth hmax : ℕ)
    (ancestors : Prefix (Representatives key) depth) (hh : ∀ d < depth, h d ≤ hmax) :
    (cursorFrames h key depth ancestors).length ≤ (4 * hmax + 4) * depth := by
  unfold cursorFrames
  have hb := flatten_length_le
    (List.ofFn fun i : Fin depth => cursorFrame (h i.val) (ancestors i).val.val).reverse
    (4 * hmax + 4) (by
      intro word hw
      rw [List.mem_reverse, List.mem_ofFn] at hw
      obtain ⟨i, rfl⟩ := hw
      rw [cursorFrame_length]
      have hi := hh i.val i.isLt
      omega)
  simpa only [List.length_reverse, List.length_ofFn, Nat.mul_comm] using hb

/-- Both persistent frame banks together use polynomially many actual bits,
including framing delimiters for empty heads. -/
theorem retainedFrames_length_le (depth levels hmax : ℕ)
    (ancestors : Prefix (Representatives key) depth) (hd : depth ≤ levels)
    (hh : ∀ d < depth, h d ≤ hmax) :
    (representativeFrames h key depth ancestors).length +
      (cursorFrames h key depth ancestors).length ≤ 6 * levels * (hmax + 1) := by
  have hr := representativeFrames_length_le h key depth hmax ancestors hh
  have hc := cursorFrames_length_le h key depth hmax ancestors hh
  have hm := Nat.mul_le_mul_right (6 * (hmax + 1)) hd
  nlinarith

end Frames

section KeyEncoding

/-- Reloading or changing the faithful physical encoding of a full key does
not change its first-occurrence candidate. The equivalence fixes every index. -/
def representativeKernelEquiv {n : ℕ} {A B : Type*}
    (actual : Fin n → A) (model : Fin n → B)
    (hkernel : ∀ i j, actual i = actual j ↔ model i = model j) :
    AttainedSignatures.Representative actual ≃ AttainedSignatures.Representative model where
  toFun i := ⟨i.val, fun j hj he => i.property j hj ((hkernel j i.val).mpr he)⟩
  invFun i := ⟨i.val, fun j hj he => i.property j hj ((hkernel j i.val).mp he)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_representative_kernel {n : ℕ} {A B : Type*}
    (actual : Fin n → A) (model : Fin n → B)
    (hkernel : ∀ i j, actual i = actual j ↔ model i = model j) :
    Nat.card (AttainedSignatures.Representative actual) =
      Nat.card (AttainedSignatures.Representative model) :=
  Nat.card_congr (representativeKernelEquiv actual model hkernel)

theorem fintype_card_representative_kernel {n : ℕ} {A B : Type*}
    (actual : Fin n → A) (model : Fin n → B)
    (hkernel : ∀ i j, actual i = actual j ↔ model i = model j) :
    Fintype.card (AttainedSignatures.Representative actual) =
      Fintype.card (AttainedSignatures.Representative model) :=
  Fintype.card_congr (representativeKernelEquiv actual model hkernel)

/-- The actual predecessor latch depends only on full-key equality. Only
the comparisons that are really visited occur in this premise. -/
theorem duplicateScan_kernel {A B : Type*} [DecidableEq A] [DecidableEq B]
    (actual : ℕ → A) (model : ℕ → B) (candidate bound : ℕ)
    (hkernel : ∀ j < bound, actual j = actual candidate ↔ model j = model candidate) :
    AttainedSignatures.duplicateScan actual candidate bound =
      AttainedSignatures.duplicateScan model candidate bound := by
  apply Bool.eq_iff_iff.mpr
  rw [AttainedSignatures.duplicateScan_eq_true_iff, AttainedSignatures.duplicateScan_eq_true_iff]
  constructor
  · rintro ⟨j, hj, he⟩
    exact ⟨j, hj, (hkernel j hj).mp he⟩
  · rintro ⟨j, hj, he⟩
    exact ⟨j, hj, (hkernel j hj).mpr he⟩

/-- The byte-key rescan's actual fresh bit is exactly the first-occurrence
predicate of the stable mathematical full signature. -/
theorem actual_fresh_iff_model {n : ℕ} {A B : Type*} [DecidableEq A]
    (actual : ℕ → A) (model : Fin n → B)
    (hkernel : ∀ i j : Fin n, actual i = actual j ↔ model i = model j)
    (candidate : Fin n) :
    (!(AttainedSignatures.duplicateScan actual candidate candidate)) = true ↔
      ∀ j, j < candidate → model j ≠ model candidate := by
  have hb : (!(AttainedSignatures.duplicateScan actual candidate candidate)) = true ↔
      AttainedSignatures.duplicateScan actual candidate candidate = false := by
    cases AttainedSignatures.duplicateScan actual candidate candidate <;> decide
  rw [hb, AttainedSignatures.rescan_emits_iff]
  constructor
  · intro hf j hj he
    exact hf j hj ((hkernel j candidate).mpr he)
  · intro hf j hj he
    exact hf j hj ((hkernel j candidate).mp he)

theorem actual_duplicate_iff_model {n : ℕ} {A B : Type*} [DecidableEq A]
    (actual : ℕ → A) (model : Fin n → B)
    (hkernel : ∀ i j : Fin n, actual i = actual j ↔ model i = model j)
    (candidate : Fin n) :
    (!(AttainedSignatures.duplicateScan actual candidate candidate)) = false ↔
      ¬ ∀ j, j < candidate → model j ≠ model candidate := by
  have hb : (!(AttainedSignatures.duplicateScan actual candidate candidate)) = false ↔
      ¬ (!(AttainedSignatures.duplicateScan actual candidate candidate)) = true := by
    cases !(AttainedSignatures.duplicateScan actual candidate candidate) <;> decide
  exact hb.trans (not_congr (actual_fresh_iff_model actual model hkernel candidate))

end KeyEncoding

section AttainedLabels

open OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments

variable {G : Type*} {A L : G → Type*} [∀ g, Fintype (A g)] [∀ g, DecidableEq (L g)]

/-- The finset subtype used by head grouping and the set-range subtype used
by first occurrences have the same actual label, with no added restriction. -/
def rangeLabelEquiv (label : ∀ g, A g → L g) (g : G) :
    Set.range (label g) ≃ LabelValue label g where
  toFun y := ⟨y.val, by
    obtain ⟨a, ha⟩ := y.property
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩⟩
  invFun y := ⟨y.val, by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp y.property
    exact ⟨a, ha⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def rangeEnumerateEquiv {count : G → ℕ}
    (enumerate : ∀ g, Fin (count g) ≃ A g) (label : ∀ g, A g → L g) (g : G) :
    Set.range (fun i ↦ label g (enumerate g i)) ≃ Set.range (label g) where
  toFun y := ⟨y.val, by
    obtain ⟨i, hi⟩ := y.property
    exact ⟨enumerate g i, hi⟩⟩
  invFun y := ⟨y.val, by
    obtain ⟨a, ha⟩ := y.property
    exact ⟨(enumerate g).symm a, by simpa using ha⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A bounded assignment enumerator reindexes attained labels without
requiring its chosen representative to satisfy a correction restriction. -/
noncomputable def representativeLabelEquiv {count : G → ℕ}
    (enumerate : ∀ g, Fin (count g) ≃ A g) (label : ∀ g, A g → L g) (g : G) :
    AttainedSignatures.Representative (fun i => label g (enumerate g i)) ≃ LabelValue label g :=
  (AttainedSignatures.representativeEquiv (fun i => label g (enumerate g i))).trans
    ((rangeEnumerateEquiv enumerate label g).trans
      (rangeLabelEquiv label g))

@[simp] theorem representativeLabelEquiv_value {count : G → ℕ}
    (enumerate : ∀ g, Fin (count g) ≃ A g) (label : ∀ g, A g → L g) (g : G)
    (rep : AttainedSignatures.Representative (fun i => label g (enumerate g i))) :
    (representativeLabelEquiv enumerate label g rep).val = label g (enumerate g rep.val) := by
  change ((AttainedSignatures.representativeEquiv
    (fun i ↦ label g (enumerate g i))) rep).val = label g (enumerate g rep.val)
  exact AttainedSignatures.representativeEquiv_value _ rep

noncomputable def representativeLabelTupleEquiv {count : G → ℕ}
    (enumerate : ∀ g, Fin (count g) ≃ A g) (label : ∀ g, A g → L g) :
    (∀ g, AttainedSignatures.Representative (fun i => label g (enumerate g i))) ≃
      (∀ g, LabelValue label g) :=
  Equiv.piCongrRight (representativeLabelEquiv enumerate label)

/-- This is exactly the attained-label sum appearing in the restricted
grouping theorem. Full raw head rescans remain inside each callback value. -/
theorem sum_representative_labels [Fintype G] {count : G → ℕ}
    (enumerate : ∀ g, Fin (count g) ≃ A g) (label : ∀ g, A g → L g)
    {R : Type*} [AddCommMonoid R] (value : (∀ g, LabelValue label g) → R) :
    (∑ reps : (∀ g, AttainedSignatures.Representative (fun i => label g (enumerate g i))),
      value (representativeLabelTupleEquiv enumerate label reps)) = ∑ labels, value labels :=
  (representativeLabelTupleEquiv enumerate label).sum_comp value

end AttainedLabels

section NativeFrames

open ExecCNFTupleEnumeration SignatureTupleProgram StructuredCalls

private theorem record_outside (a : StructuredProgram.State 40 896) (i : Fin 896)
    (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (recordRepresentativeState a).stacks i = a.stacks i := by
  unfold recordRepresentativeState
  rw [pushWordState_outside _ _ _ _ _ hp hr]
  simp [copyState, StackRoutines.copyStacks, hp]

private theorem save_outside (a : StructuredProgram.State 40 896) (i : Fin 896)
    (hf : i ≠ tupleStacks 0) (hc : i ≠ tupleStacks 2) (hr : i ≠ tupleStacks 7) :
    (saveCursorState a).stacks i = a.stacks i := by
  unfold saveCursorState
  rw [pushWordState_outside _ _ _ _ _ hr hf, pushWordState_outside _ _ _ _ _ hc hf]

private theorem drop_outside (a : StructuredProgram.State 40 896) (word reps : List Bool)
    (i : Fin 896) (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (dropRepresentativeState a word reps).stacks i = a.stacks i := by
  change Function.update (popWordState _ _ _ a word reps).stacks (tupleStacks 4) [] i = _
  rw [Function.update_of_ne hp, popWordState_outside _ _ _ _ _ _ _ hr hp]

private theorem restore_outside (a : StructuredProgram.State 40 896)
    (candidate remaining frames : List Bool) (i : Fin 896)
    (hf : i ≠ tupleStacks 0) (hc : i ≠ tupleStacks 2) (hr : i ≠ tupleStacks 7) :
    (restoreCursorState a candidate remaining frames).stacks i = a.stacks i := by
  unfold restoreCursorState
  rw [popWordState_outside _ _ _ _ _ _ _ hf hc,
    popWordState_outside _ _ _ _ _ _ _ hf hr]

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- The actual record-then-save commands install precisely the dependent
child prefix in both persistent banks and empty their consumed words. -/
theorem retainFrames_state (depth : ℕ) (ancestors : Prefix (Representatives key) depth)
    (rep : Representatives key depth) (a : StructuredProgram.State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key depth ancestors)
    (hr : a.stacks (tupleStacks 1) = representativeFrames h key depth ancestors)
    (hc : a.stacks (tupleStacks 2) = fixedBits (h depth) rep.val.val)
    (hn : a.stacks (tupleStacks 7) = fixedBits (h depth + 1) (2 ^ h depth - rep.val.val))
    (hp : a.stacks (tupleStacks 4) = []) :
    let b := saveCursorState (recordRepresentativeState a)
    b.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) (Fin.snoc ancestors rep) ∧
    b.stacks (tupleStacks 1) = representativeFrames h key (depth + 1) (Fin.snoc ancestors rep) ∧
    b.stacks (tupleStacks 2) = [] ∧ b.stacks (tupleStacks 7) = [] ∧
    b.stacks (tupleStacks 4) = [] := by
  dsimp only
  have hs := saveCursorState_words (recordRepresentativeState a)
  have hrec := recordRepresentativeState_words a hp
  refine ⟨?_, ?_, hs.1, hs.2.1, ?_⟩
  · rw [hs.2.2, hrec.2.1, record_outside a (tupleStacks 7) (by decide) (by decide),
      record_outside a (tupleStacks 0) (by decide) (by decide), hc, hn, hf,
      cursorFrames_snoc, cursorFrame]
  · rw [save_outside _ (tupleStacks 1) (by decide) (by decide) (by decide),
      hrec.1, hc, hr, representativeFrames_snoc]
  · rw [save_outside _ (tupleStacks 4) (by decide) (by decide) (by decide), hrec.2.2]

theorem retainFrames_eval (width candidate : ℕ) (a : StructuredProgram.State 40 896)
    (hc : a.stacks (tupleStacks 2) = fixedBits width candidate)
    (hn : a.stacks (tupleStacks 7) = fixedBits (width + 1) (2 ^ width - candidate))
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = []) :
    Eval (.seq recordRepresentativeCommand saveCursorCommand) (22 * width + 25) a
      (saveCursorState (recordRepresentativeState a)) := by
  have he := (recordRepresentative_eval a hp ht).seq
    (saveCursor_eval (recordRepresentativeState a))
  rw [(recordRepresentativeState_words a hp).2.1,
    record_outside a (tupleStacks 7) (by decide) (by decide), hc, hn] at he
  simp only [fixedBits_length] at he
  convert he using 1
  omega

/-- Dropping the just-finished representative and restoring the two saved
cursor words gives exactly `Fin.init`, before the paid parent increment. -/
theorem returnFrames_state (depth : ℕ) (ancestors : Prefix (Representatives key) (depth + 1))
    (a : StructuredProgram.State 40 896) :
    let word := fixedBits (h depth) (ancestors (Fin.last depth)).val.val
    let remaining := fixedBits (h depth + 1) (2 ^ h depth - (ancestors (Fin.last depth)).val.val)
    let reps := representativeFrames h key depth (Fin.init ancestors)
    let frames := cursorFrames h key depth (Fin.init ancestors)
    let b := restoreCursorState (dropRepresentativeState a word reps) word remaining frames
    b.stacks (tupleStacks 0) = frames ∧ b.stacks (tupleStacks 1) = reps ∧
    b.stacks (tupleStacks 2) = word ∧ b.stacks (tupleStacks 7) = remaining ∧
    b.stacks (tupleStacks 4) = [] := by
  dsimp only
  have hs := restoreCursorState_words
    (dropRepresentativeState a
      (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
      (representativeFrames h key depth (Fin.init ancestors)))
    (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (fixedBits (h depth + 1) (2 ^ h depth - (ancestors (Fin.last depth)).val.val))
    (cursorFrames h key depth (Fin.init ancestors))
  refine ⟨hs.2.2, ?_, hs.1, hs.2.1, ?_⟩
  · rw [restore_outside _ _ _ _ (tupleStacks 1) (by decide) (by decide) (by decide)]
    exact (dropRepresentativeState_stacks _ _ _).1
  · rw [restore_outside _ _ _ _ (tupleStacks 4) (by decide) (by decide) (by decide)]
    exact (dropRepresentativeState_stacks _ _ _).2

theorem returnFrames_eval (depth : ℕ) (ancestors : Prefix (Representatives key) (depth + 1))
    (a : StructuredProgram.State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) ancestors)
    (hr : a.stacks (tupleStacks 1) = representativeFrames h key (depth + 1) ancestors)
    (hc : a.stacks (tupleStacks 2) = []) (hn : a.stacks (tupleStacks 7) = [])
    (hp : a.stacks (tupleStacks 4) = []) :
    let word := fixedBits (h depth) (ancestors (Fin.last depth)).val.val
    let remaining := fixedBits (h depth + 1) (2 ^ h depth - (ancestors (Fin.last depth)).val.val)
    let reps := representativeFrames h key depth (Fin.init ancestors)
    let frames := cursorFrames h key depth (Fin.init ancestors)
    Eval (.seq dropRepresentativeCommand restoreCursorCommand) (20 * h depth + 21) a
      (restoreCursorState (dropRepresentativeState a word reps) word remaining frames) := by
  dsimp only
  have hd := dropRepresentative_eval a
    (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (representativeFrames h key depth (Fin.init ancestors))
    (hr.trans (representativeFrames_pop h key depth ancestors)) hp
  have hs := restoreCursor_eval (dropRepresentativeState a
    (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (representativeFrames h key depth (Fin.init ancestors)))
    (fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (fixedBits (h depth + 1) (2 ^ h depth - (ancestors (Fin.last depth)).val.val))
    (cursorFrames h key depth (Fin.init ancestors)) (by
      rw [drop_outside _ _ _ (tupleStacks 0) (by decide) (by decide), hf,
        cursorFrames_pop, cursorFrame])
    (by rw [drop_outside _ _ _ (tupleStacks 2) (by decide) (by decide), hc])
    (by rw [drop_outside _ _ _ (tupleStacks 7) (by decide) (by decide), hn])
  have he := hd.seq hs
  simp only [fixedBits_length] at he
  convert he using 1
  omega

end NativeFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
