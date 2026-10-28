import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNF
import OAI.Algorithms.SubexponentialSAT.Sunflower

namespace OAI.Algorithms

/-! Explicit finite sunflower search, with counted list scans. -/
namespace SubexponentialSAT.ExecSunflowerSearch

/-- First successful Boolean test, together with the actual number of tests run. -/
def scan {α : Type*} (p : α → Bool) : List α → Option α × ℕ
  | [] => (none, 0)
  | a :: as => if p a then (some a, 1)
      else let r := scan p as; (r.1, r.2 + 1)

theorem scan_count_le {α : Type*} (p : α → Bool) (as : List α) :
    (scan p as).2 ≤ as.length := by
  induction as with
  | nil => simp [scan]
  | cons a as ih =>
      cases hp : p a with
      | false => simpa [scan, hp] using Nat.succ_le_succ ih
      | true => simp [scan, hp]

theorem scan_none_iff {α : Type*} (p : α → Bool) (as : List α) :
    (scan p as).1 = none ↔ ∀ a ∈ as, p a = false := by
  induction as with
  | nil => simp [scan]
  | cons a as ih =>
      cases hp : p a <;> simp [scan, hp, ih]

theorem scan_some {α : Type*} (p : α → Bool) (as : List α) {a : α}
    (h : (scan p as).1 = some a) : a ∈ as ∧ p a = true := by
  induction as with
  | nil => simp [scan] at h
  | cons b bs ih =>
      cases hp : p b with
      | false =>
          have ht : (scan p bs).1 = some a := by simpa [scan, hp] using h
          obtain ⟨ha, hpa⟩ := ih ht
          exact ⟨List.mem_cons_of_mem b ha, hpa⟩
      | true =>
          have hab : b = a := by simpa [scan, hp] using h
          subst b
          exact ⟨List.mem_cons_self, hp⟩

/-- Scan consecutive widths, counting all candidate tests executed. -/
def scanWidths {α : Type*} (find : ℕ → Option α × ℕ) :
    ℕ → ℕ → Option (ℕ × α) × ℕ
  | _, 0 => (none, 0)
  | start, fuel + 1 =>
      let r := find start
      match r.1 with
      | some a => (some (start, a), r.2)
      | none => let tail := scanWidths find (start + 1) fuel
                (tail.1, r.2 + tail.2)

theorem scanWidths_none_iff {α : Type*} (find : ℕ → Option α × ℕ)
    (start fuel : ℕ) :
    (scanWidths find start fuel).1 = none ↔
      ∀ d, start ≤ d → d < start + fuel → (find d).1 = none := by
  induction fuel generalizing start with
  | zero =>
      constructor
      · intro _ d hsd hd
        omega
      · intro _
        rfl
  | succ fuel ih =>
      cases hf : (find start).1 with
      | none =>
          simp only [scanWidths, hf, ih]
          constructor
          · intro h d hsd hd
            by_cases he : d = start
            · simpa [he] using hf
            · exact h d (by omega) (by omega)
          · intro h d hsd hd
            exact h d (by omega) (by omega)
      | some a =>
          simp only [scanWidths, hf, reduceCtorEq, false_iff]
          intro h
          have := h start le_rfl (by omega)
          simp [hf] at this

theorem scanWidths_some {α : Type*} (find : ℕ → Option α × ℕ)
    (start fuel : ℕ) {d : ℕ} {a : α}
    (h : (scanWidths find start fuel).1 = some (d, a)) :
    start ≤ d ∧ d < start + fuel ∧ (find d).1 = some a ∧
      ∀ j, start ≤ j → j < d → (find j).1 = none := by
  induction fuel generalizing start with
  | zero => simp [scanWidths] at h
  | succ fuel ih =>
      cases hf : (find start).1 with
      | none =>
          have ht : (scanWidths find (start + 1) fuel).1 = some (d, a) := by
            simpa [scanWidths, hf] using h
          obtain ⟨hsd, hd, hfind, hmin⟩ := ih (start + 1) ht
          refine ⟨by omega, by omega, hfind, ?_⟩
          intro j hsj hjd
          by_cases he : j = start
          · simpa [he] using hf
          · exact hmin j (by omega) hjd
      | some b =>
          have he : (start, b) = (d, a) := by simpa [scanWidths, hf] using h
          have hsd := congrArg Prod.fst he
          have hba := congrArg Prod.snd he
          simp only at hsd hba
          subst d
          subst b
          exact ⟨le_rfl, by omega, hf, by intro j hsj hjd; omega⟩

theorem scanWidths_count_le {α : Type*} (find : ℕ → Option α × ℕ)
    (start fuel bound : ℕ)
    (hbound : ∀ d, start ≤ d → d < start + fuel → (find d).2 ≤ bound) :
    (scanWidths find start fuel).2 ≤ fuel * bound := by
  induction fuel generalizing start with
  | zero => simp [scanWidths]
  | succ fuel ih =>
      have hs := hbound start le_rfl (by omega)
      cases hf : (find start).1 with
      | none =>
          have ht := ih (start + 1) (by
            intro d hsd hd
            exact hbound d (by omega) (by omega))
          simp only [scanWidths, hf]
          calc
            (find start).2 + (scanWidths find (start + 1) fuel).2 ≤
                bound + fuel * bound := Nat.add_le_add hs ht
            _ = (fuel + 1) * bound := by rw [Nat.add_mul, Nat.one_mul]; omega
      | some a =>
          simp only [scanWidths, hf]
          exact hs.trans (by rw [Nat.add_mul, Nat.one_mul]; omega)



/-- An explicit fixed-size generator records recursive calls and outer-list cells
visited by its append/map operations. -/
structure FixedEnumeration (α : Type*) where
  values : List (List α)
  calls : ℕ
  cells : ℕ

def enumerateFixed {α : Type*} : ℕ → List α → FixedEnumeration α
  | 0, _ => ⟨[[]], 1, 0⟩
  | _ + 1, [] => ⟨[], 1, 0⟩
  | r + 1, a :: as =>
      let left := enumerateFixed (r + 1) as
      let right := enumerateFixed r as
      ⟨left.values ++ right.values.map (List.cons a),
        left.calls + right.calls + 1,
        left.cells + right.cells + left.values.length + right.values.length⟩

@[simp] theorem enumerateFixed_values {α : Type*} (r : ℕ) (as : List α) :
    (enumerateFixed r as).values = as.sublistsLen r := by
  induction as generalizing r with
  | nil => cases r <;> simp [enumerateFixed]
  | cons a as ih =>
      cases r <;> simp [enumerateFixed, List.sublistsLen_succ_cons, ih]

@[simp] theorem enumerateFixed_length {α : Type*} (r : ℕ) (as : List α) :
    (enumerateFixed r as).values.length = as.length.choose r := by
  rw [enumerateFixed_values, List.length_sublistsLen]

/-- Failed branches are included: this bound is on actual recursive calls, even
when the requested size exceeds the input length and the output is empty. -/
theorem enumerateFixed_calls_le {α : Type*} (r : ℕ) (as : List α) :
    (enumerateFixed r as).calls + 1 ≤ 2 * (as.length + 1) ^ r := by
  induction as generalizing r with
  | nil => cases r <;> simp [enumerateFixed]
  | cons a as ih =>
      cases r with
      | zero => simp [enumerateFixed]
      | succ r =>
          have hl := ih (r + 1)
          have hr := ih r
          change (enumerateFixed (r + 1) as).calls + (enumerateFixed r as).calls + 1 + 1 ≤
            2 * (as.length + 1 + 1) ^ (r + 1)
          calc
            _ ≤ 2 * (as.length + 1) ^ (r + 1) + 2 * (as.length + 1) ^ r := by omega
            _ = 2 * ((as.length + 1) ^ r * (as.length + 1 + 1)) := by
              rw [pow_succ]
              ring
            _ ≤ 2 * ((as.length + 1 + 1) ^ r * (as.length + 1 + 1)) :=
              Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _
                (Nat.pow_le_pow_left (Nat.le_succ _) r))
            _ = 2 * (as.length + 1 + 1) ^ (r + 1) := by rw [pow_succ]

/-- Every map/append cell traversal is charged, independently of output size. -/
theorem enumerateFixed_cells_le {α : Type*} (r : ℕ) (as : List α) :
    (enumerateFixed r as).cells ≤
      (enumerateFixed r as).calls * (as.length + 1) ^ r := by
  induction as generalizing r with
  | nil => cases r <;> simp [enumerateFixed]
  | cons a as ih =>
      cases r with
      | zero => simp [enumerateFixed]
      | succ r =>
          let left := enumerateFixed (r + 1) as
          let right := enumerateFixed r as
          let B := (as.length + 1 + 1) ^ (r + 1)
          have hl : left.cells ≤ left.calls * B := by
            exact (ih (r + 1)).trans (Nat.mul_le_mul_left _
              (Nat.pow_le_pow_left (Nat.le_succ _) (r + 1)))
          have hr : right.cells ≤ right.calls * B := by
            apply (ih r).trans
            apply Nat.mul_le_mul_left
            exact (Nat.pow_le_pow_left (Nat.le_succ (as.length + 1)) r).trans
              (Nat.pow_le_pow_right (by omega) (Nat.le_succ r))
          have hlen : left.values.length + right.values.length ≤ B := by
            have he : (enumerateFixed (r + 1) (a :: as)).values.length =
                left.values.length + right.values.length := by
              simp only [enumerateFixed, List.length_append, List.length_map]
              rfl
            rw [← he, enumerateFixed_length]
            exact (Nat.choose_le_pow _ _).trans
              (Nat.pow_le_pow_left (Nat.le_succ (a :: as).length) (r + 1))
          change left.cells + right.cells + left.values.length + right.values.length ≤
            (left.calls + right.calls + 1) * B
          calc
            _ ≤ left.calls * B + right.calls * B + B := by omega
            _ = (left.calls + right.calls + 1) * B := by ring

theorem enumerateFixed_cells_bound {α : Type*} (r : ℕ) (as : List α) :
    (enumerateFixed r as).cells ≤ 2 * (as.length + 1) ^ (2 * r) := by
  apply (enumerateFixed_cells_le r as).trans
  have hc : (enumerateFixed r as).calls ≤ 2 * (as.length + 1) ^ r :=
    (Nat.le_succ _).trans (enumerateFixed_calls_le r as)
  calc
    _ ≤ (2 * (as.length + 1) ^ r) * (as.length + 1) ^ r :=
      Nat.mul_le_mul_right _ hc
    _ = 2 * (as.length + 1) ^ (2 * r) := by rw [show 2 * r = r + r by omega, pow_add]; ring


/-- Enumerate all sublists of one clause, recording the recursion and map/append loops. -/
def enumerateCores {α : Type*} : List α → FixedEnumeration α
  | [] => ⟨[[]], 1, 0⟩
  | a :: as =>
      let tail := enumerateCores as
      ⟨tail.values ++ tail.values.map (List.cons a), tail.calls + 1,
        tail.cells + 2 * tail.values.length⟩

@[simp] theorem enumerateCores_values {α : Type*} (as : List α) :
    (enumerateCores as).values = as.sublists' := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [enumerateCores, List.sublists'_cons, ih]

@[simp] theorem enumerateCores_length {α : Type*} (as : List α) :
    (enumerateCores as).values.length = 2 ^ as.length := by
  rw [enumerateCores_values, List.length_sublists']

@[simp] theorem enumerateCores_calls {α : Type*} (as : List α) :
    (enumerateCores as).calls = as.length + 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [enumerateCores, ih]

theorem enumerateCores_cells_exact {α : Type*} (as : List α) :
    (enumerateCores as).cells + 2 = 2 * 2 ^ as.length := by
  induction as with
  | nil => simp [enumerateCores]
  | cons a as ih =>
      simp only [enumerateCores, enumerateCores_length, List.length_cons]
      rw [pow_succ]
      omega

/-- Enumerate clause cores for a whole input, counting the outer concatenations too. -/
def enumerateCoreFamily {α : Type*} : List (List α) → FixedEnumeration α
  | [] => ⟨[], 1, 0⟩
  | C :: F =>
      let head := enumerateCores C
      let tail := enumerateCoreFamily F
      ⟨head.values ++ tail.values, head.calls + tail.calls + 1,
        head.cells + tail.cells + head.values.length⟩

theorem enumerateCoreFamily_values {α : Type*} (F : List (List α)) :
    (enumerateCoreFamily F).values = F.flatMap List.sublists' := by
  induction F with
  | nil => rfl
  | cons C F ih => simp [enumerateCoreFamily, ih]

theorem enumerateCoreFamily_calls_le {α : Type*} (F : List (List α)) (k : ℕ)
    (hWidth : ∀ C ∈ F, C.length ≤ k) :
    (enumerateCoreFamily F).calls ≤ F.length * (k + 2) + 1 := by
  induction F with
  | nil => simp [enumerateCoreFamily]
  | cons C F ih =>
      have hC := hWidth C List.mem_cons_self
      have hF := ih (fun D hD => hWidth D (List.mem_cons_of_mem C hD))
      simp only [enumerateCoreFamily, enumerateCores_calls, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem enumerateCoreFamily_cells_le {α : Type*} (F : List (List α)) (k : ℕ)
    (hWidth : ∀ C ∈ F, C.length ≤ k) :
    (enumerateCoreFamily F).cells ≤ 3 * F.length * 2 ^ k := by
  induction F with
  | nil => simp [enumerateCoreFamily]
  | cons C F ih =>
      have hC := hWidth C List.mem_cons_self
      have hp : 2 ^ C.length ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hC
      have hc := enumerateCores_cells_exact C
      have hF := ih (fun D hD => hWidth D (List.mem_cons_of_mem C hD))
      simp only [enumerateCoreFamily, enumerateCores_length, List.length_cons]
      calc
        _ ≤ 2 * 2 ^ k + 3 * F.length * 2 ^ k + 2 ^ k := by omega
        _ = 3 * (F.length + 1) * 2 ^ k := by ring

open ExecCNF
open scoped BigOperators

variable {α : Type*} [DecidableEq α]

abbrev Candidate (α : Type*) := Formula α × Clause α

/-- Literal intersection is implemented by a filter and linear membership scans. -/
def intersection (C D : Clause α) : Clause α :=
  C.filter (fun x => contains x D)

@[simp] theorem clauseSet_intersection (C D : Clause α) :
    clauseSet (intersection C D) = clauseSet C ∩ clauseSet D := by
  ext x
  simp [intersection]

/-- Petals as executable literal-list differences. -/
def petals (c : Candidate α) : Formula α :=
  c.1.map (fun C => C.filter (fun x => !(contains x c.2)))

/-- All conditions are checked by finite list scans. Distinctness is enforced by
counting the extensional clause deduplication, not raw repeated occurrences. -/
def check (F : Formula α) (z : ℕ → ℕ) (d : ℕ) (c : Candidate α) : Bool :=
  c.1.all (fun C => F.any (fun D => equivalent C D)) &&
  decide ((dedupClauses c.1).length = z d) &&
  !(c.2.isEmpty) &&
  c.1.all (fun C => subset c.2 C && decide ((dedupLiterals C).length = d)) &&
  c.1.all (fun C => c.1.all (fun D =>
    equivalent C D || equivalent (intersection C D) c.2))

/-- Mathematical specification of a candidate; execution uses `check`. -/
def Good (F : Formula α) (z : ℕ → ℕ) (d : ℕ) (c : Candidate α) : Prop :=
  formulaSet c.1 ⊆ formulaSet F ∧ (formulaSet c.1).card = z d ∧
  (clauseSet c.2).Nonempty ∧
  Sunflower.IsSunflowerWithCore (formulaSet c.1) (clauseSet c.2) ∧
  ∀ C ∈ formulaSet c.1, C.card = d

@[simp] theorem dedupLiterals_length (C : Clause α) :
    (dedupLiterals C).length = (clauseSet C).card := by
  have h := List.toFinset_card_of_nodup (dedupLiterals_nodup C)
  change (clauseSet (dedupLiterals C)).card = _ at h
  rw [clauseSet_dedupLiterals] at h
  exact h.symm

@[simp] theorem dedupClauses_length (F : Formula α) :
    (dedupClauses F).length = (formulaSet F).card := by
  have h := List.toFinset_card_of_nodup (dedupClauses_map_nodup F)
  change (formulaSet (dedupClauses F)).card = _ at h
  rw [formulaSet_dedupClauses, List.length_map] at h
  exact h.symm

theorem forall_formulaSet_iff (F : Formula α) (P : Finset α → Prop) :
    (∀ C ∈ formulaSet F, P C) ↔ ∀ C ∈ F, P (clauseSet C) := by
  constructor
  · intro h C hC
    exact h _ (mem_formulaSet.mpr ⟨C, hC, rfl⟩)
  · intro h C hC
    obtain ⟨D, hD, rfl⟩ := mem_formulaSet.mp hC
    exact h D hD

@[simp] theorem core_nonempty_iff (H : Clause α) :
    (clauseSet H).Nonempty ↔ H.isEmpty = false := by
  cases H with
  | nil => simp
  | cons x xs => simp

@[simp] theorem check_true_iff (F : Formula α) (z : ℕ → ℕ) (d : ℕ)
    (c : Candidate α) : check F z d c = true ↔ Good F z d c := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, any_equivalent_true,
    decide_eq_true_eq, dedupClauses_length, subset_true,
    dedupLiterals_length, Bool.or_eq_true, equivalent_true, clauseSet_intersection]
  constructor
  · rintro ⟨⟨⟨⟨hsub, hcard⟩, hnonempty⟩, hsets⟩, hpairs⟩
    refine ⟨?_, hcard, (core_nonempty_iff _).mpr (by simpa using hnonempty), ⟨?_, ?_⟩, ?_⟩
    · exact (forall_formulaSet_iff _ _).mpr hsub
    · exact (forall_formulaSet_iff _ _).mpr (fun C hC => (hsets C hC).1)
    · intro C hC D hD hne
      obtain ⟨C', hC', rfl⟩ := mem_formulaSet.mp hC
      obtain ⟨D', hD', rfl⟩ := mem_formulaSet.mp hD
      exact (hpairs C' hC' D' hD').resolve_left hne
    · exact (forall_formulaSet_iff _ _).mpr (fun C hC => (hsets C hC).2)
  · rintro ⟨hsub, hcard, hnonempty, ⟨hcore, hpairs⟩, hwidth⟩
    refine ⟨⟨⟨⟨?_, hcard⟩, (by simpa using (core_nonempty_iff _).mp hnonempty)⟩, ?_⟩, ?_⟩
    · exact (forall_formulaSet_iff _ _).mp hsub
    · intro C hC
      have hc : clauseSet C ∈ formulaSet c.1 := mem_formulaSet.mpr ⟨C, hC, rfl⟩
      exact ⟨hcore _ hc, hwidth _ hc⟩
    · intro C hC D hD
      by_cases he : clauseSet C = clauseSet D
      · exact Or.inl he
      · exact Or.inr (hpairs _ (mem_formulaSet.mpr ⟨C, hC, rfl⟩)
          _ (mem_formulaSet.mpr ⟨D, hD, rfl⟩) he)

/-- Cores are sublists of individual clauses; no formula powerset is generated. -/
def coreCandidates (F : Formula α) : List (Clause α) :=
  (enumerateCoreFamily F).values

/-- Form the Cartesian product by explicit map/append loops. The count charges
one recursive call and each map/append list-cell visit. -/
def pairLists {β γ : Type*} : List β → List γ → List (β × γ) × ℕ
  | [], _ => ([], 1)
  | x :: xs, ys =>
      let tail := pairLists xs ys
      (ys.map (fun y => (x, y)) ++ tail.1, tail.2 + 2 * ys.length + 1)

@[simp] theorem pairLists_values {β γ : Type*} (xs : List β) (ys : List γ) :
    (pairLists xs ys).1 = xs.flatMap (fun x => ys.map (fun y => (x, y))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairLists, ih]

@[simp] theorem pairLists_count {β γ : Type*} (xs : List β) (ys : List γ) :
    (pairLists xs ys).2 = xs.length * (2 * ys.length + 1) + 1 := by
  induction xs with
  | nil => simp [pairLists]
  | cons x xs ih => simp only [pairLists, ih, List.length_cons]; ring

/-- Structural generation work: recursive calls and map/append cell visits.
The extensional clause-deduplication comparisons are counted separately by the
measured CNF primitives; candidate predicate tests are also separate. -/
def buildCandidates (F : Formula α) (z : ℕ → ℕ) (d : ℕ) :
    List (Candidate α) × ℕ :=
  let families := enumerateFixed (z d) (dedupClauses F)
  let cores := enumerateCoreFamily F
  let pairs := pairLists families.values cores.values
  (pairs.1, families.calls + families.cells + cores.calls + cores.cells + pairs.2)

/-- Direct fixed-cardinality subfamily generation followed by core candidates. -/
def candidates (F : Formula α) (z : ℕ → ℕ) (d : ℕ) : List (Candidate α) :=
  (buildCandidates F z d).1

theorem candidates_eq (F : Formula α) (z : ℕ → ℕ) (d : ℕ) :
    candidates F z d = (enumerateFixed (z d) (dedupClauses F)).values.flatMap
      (fun G => (coreCandidates F).map (fun H => (G, H))) := by
  simp only [candidates, buildCandidates, pairLists_values, coreCandidates]

/-- Search one width and count actual calls to the complete Boolean predicate. -/
def searchAt (F : Formula α) (z : ℕ → ℕ) (d : ℕ) : Option (Candidate α) × ℕ :=
  scan (check F z d) (candidates F z d)

/-- Widths are visited in the fixed order 2, 3, ..., k. -/
def select (F : Formula α) (z : ℕ → ℕ) (k : ℕ) :
    Option (ℕ × Candidate α) × ℕ :=
  scanWidths (searchAt F z) 2 (k - 1)


/-- Restrict the extensionally deduplicated list to a specified finite family. -/
def subfamilyList (F : Formula α) (G : Finset (Finset α)) : Formula α :=
  (dedupClauses F).filter (fun C => decide (clauseSet C ∈ G))

theorem subfamilyList_sublist (F : Formula α) (G : Finset (Finset α)) :
    (subfamilyList F G).Sublist (dedupClauses F) := List.filter_sublist

theorem formulaSet_subfamilyList (F : Formula α) (G : Finset (Finset α))
    (hG : G ⊆ formulaSet F) : formulaSet (subfamilyList F G) = G := by
  ext C
  constructor
  · intro hC
    obtain ⟨D, hD, rfl⟩ := mem_formulaSet.mp hC
    exact of_decide_eq_true (List.mem_filter.mp hD).2
  · intro hC
    have hCF : C ∈ formulaSet (dedupClauses F) := by
      rw [formulaSet_dedupClauses]
      exact hG hC
    obtain ⟨D, hD, he⟩ := mem_formulaSet.mp hCF
    apply mem_formulaSet.mpr
    refine ⟨D, List.mem_filter.mpr ⟨hD, ?_⟩, he⟩
    exact decide_eq_true (he ▸ hC)

theorem subfamilyList_length (F : Formula α) (G : Finset (Finset α))
    (hG : G ⊆ formulaSet F) : (subfamilyList F G).length = G.card := by
  have hN : ((subfamilyList F G).map clauseSet).Nodup :=
    (dedupClauses_map_nodup F).sublist ((subfamilyList_sublist F G).map clauseSet)
  have hc := List.toFinset_card_of_nodup hN
  change (formulaSet (subfamilyList F G)).card = _ at hc
  rw [formulaSet_subfamilyList F G hG, List.length_map] at hc
  exact hc.symm

/-- A finite literal subset of a clause has a concrete sublist representative. -/
theorem exists_coreList {H : Finset α} {C : Clause α} (hHC : H ⊆ clauseSet C) :
    ∃ L : Clause α, L.Sublist C ∧ clauseSet L = H := by
  let L := C.filter (fun x => decide (x ∈ H))
  refine ⟨L, List.filter_sublist, ?_⟩
  ext x
  simp only [L, mem_clauseSet, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨mem_clauseSet.mp (hHC h), h⟩

/-- Every set-theoretic sunflower is represented by an enumerated list candidate. -/
theorem candidate_complete (F : Formula α) (z : ℕ → ℕ) (d : ℕ)
    (hz : 2 ≤ z d) {G : Finset (Finset α)} {H : Finset α}
    (hGF : G ⊆ formulaSet F) (hcard : G.card = z d) (hH : H.Nonempty)
    (hflower : Sunflower.IsSunflowerWithCore G H)
    (hwidth : ∀ C ∈ G, C.card = d) :
    ∃ c ∈ candidates F z d, Good F z d c := by
  have hGN : G.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨C, hCG⟩ := hGN
  obtain ⟨Craw, hCraw, hCeq⟩ := mem_formulaSet.mp (hGF hCG)
  have hHC : H ⊆ clauseSet Craw := by rw [hCeq]; exact hflower.1 C hCG
  obtain ⟨Hraw, hHraw, hHeq⟩ := exists_coreList hHC
  let Graw := subfamilyList F G
  have hGeq : formulaSet Graw = G := formulaSet_subfamilyList F G hGF
  have hGlen : Graw.length = z d := (subfamilyList_length F G hGF).trans hcard
  have hGmem : Graw ∈ (enumerateFixed (z d) (dedupClauses F)).values := by
    simpa using (List.mem_sublistsLen.mpr ⟨subfamilyList_sublist F G, hGlen⟩)
  have hHmem : Hraw ∈ coreCandidates F := by
    rw [coreCandidates, enumerateCoreFamily_values]
    apply List.mem_flatMap.mpr
    exact ⟨Craw, hCraw, List.mem_sublists'.mpr hHraw⟩
  refine ⟨(Graw, Hraw), ?_, ?_⟩
  · rw [candidates_eq]
    apply List.mem_flatMap.mpr
    exact ⟨Graw, hGmem, List.mem_map.mpr ⟨Hraw, hHmem, rfl⟩⟩
  · simp only [Good, hGeq, hHeq]
    exact ⟨hGF, hcard, hH, hflower, hwidth⟩

/-- The terminality criterion at a single width. -/
def FreeAt (F : Formula α) (z : ℕ → ℕ) (d : ℕ) : Prop :=
  Sunflower.NonemptyCoreSunflowerFree
    ((formulaSet F).filter (fun C => C.card = d)) (z d)

theorem searchAt_some (F : Formula α) (z : ℕ → ℕ) (d : ℕ) {c : Candidate α}
    (h : (searchAt F z d).1 = some c) :
    c ∈ candidates F z d ∧ Good F z d c := by
  obtain ⟨hmem, hcheck⟩ := scan_some (check F z d) (candidates F z d) h
  exact ⟨hmem, (check_true_iff F z d c).mp hcheck⟩

theorem searchAt_none_iff (F : Formula α) (z : ℕ → ℕ) (d : ℕ)
    (hz : 2 ≤ z d) : (searchAt F z d).1 = none ↔ FreeAt F z d := by
  rw [searchAt, scan_none_iff]
  constructor
  · intro h G hG hcard H hH hflower
    have hGF : G ⊆ formulaSet F := fun C hC => (Finset.mem_filter.mp (hG hC)).1
    have hw : ∀ C ∈ G, C.card = d := fun C hC => (Finset.mem_filter.mp (hG hC)).2
    obtain ⟨c, hc, hg⟩ := candidate_complete F z d hz hGF hcard hH hflower hw
    have ht := (check_true_iff F z d c).mpr hg
    have hf := h c hc
    simp [ht] at hf
  · intro h c hc
    cases ht : check F z d c with
    | false => rfl
    | true =>
        obtain ⟨hGF, hcard, hH, hflower, hw⟩ := (check_true_iff F z d c).mp ht
        exact False.elim (h (formulaSet c.1)
          (fun C hC => Finset.mem_filter.mpr ⟨hGF hC, hw C hC⟩)
          hcard (clauseSet c.2) hH hflower)

theorem select_none_iff (F : Formula α) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) :
    (select F z k).1 = none ↔ ∀ d, 2 ≤ d → d ≤ k → FreeAt F z d := by
  rw [select, scanWidths_none_iff]
  constructor
  · intro h d hd hdk
    exact (searchAt_none_iff F z d (hz d hd)).mp (h d hd (by omega))
  · intro h d hd hdk
    exact (searchAt_none_iff F z d (hz d hd)).mpr (h d hd (by omega))

theorem select_some (F : Formula α) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) {d : ℕ} {c : Candidate α}
    (h : (select F z k).1 = some (d, c)) :
    2 ≤ d ∧ d ≤ k ∧ Good F z d c ∧
      ∀ j, 2 ≤ j → j < d → FreeAt F z j := by
  obtain ⟨hd, hdk, hfound, hmin⟩ := scanWidths_some (searchAt F z) 2 (k - 1) h
  refine ⟨hd, by omega, (searchAt_some F z d hfound).2, ?_⟩
  intro j hj hjd
  exact (searchAt_none_iff F z j (hz j hj)).mp (hmin j hj hjd)


@[simp] theorem clauseSet_difference (C H : Clause α) :
    clauseSet (C.filter (fun x => !(contains x H))) = clauseSet C \ clauseSet H := by
  ext x
  simp [Bool.eq_false_iff]

/-- Executable petals match the finite-set petals used by the branching proof. -/
theorem petals_set (c : Candidate α) :
    formulaSet (petals c) = (formulaSet c.1).image (fun C => C \ clauseSet c.2) := by
  ext P
  simp only [petals, mem_formulaSet, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨L, ⟨C, hC, rfl⟩, he⟩
    exact ⟨clauseSet C, ⟨C, hC, rfl⟩, by simpa using he⟩
  · rintro ⟨C, ⟨L, hL, rfl⟩, he⟩
    exact ⟨L.filter (fun x => !(contains x c.2)), ⟨L, hL, rfl⟩, by simpa using he⟩

/-- Raw list-width assumption used in the enumeration bounds. -/
def RawWidthAtMost (k : ℕ) (F : Formula α) : Prop := ∀ C ∈ F, C.length ≤ k

omit [DecidableEq α] in
theorem coreCandidates_length_le (F : Formula α) (k : ℕ)
    (hWidth : RawWidthAtMost k F) : (coreCandidates F).length ≤ F.length * 2 ^ k := by
  induction F with
  | nil => simp [coreCandidates, enumerateCoreFamily]
  | cons C F ih =>
      have hC := hWidth C List.mem_cons_self
      have hF : RawWidthAtMost k F := fun D hD => hWidth D (List.mem_cons_of_mem C hD)
      have hI := ih hF
      simp only [coreCandidates, enumerateCoreFamily, List.length_append, List.length_cons]
      rw [enumerateCores_length]
      calc
        _ ≤ 2 ^ k + F.length * 2 ^ k :=
          Nat.add_le_add (Nat.pow_le_pow_right (by decide) hC) hI
        _ = (F.length + 1) * 2 ^ k := by rw [Nat.add_mul, Nat.one_mul]; omega

theorem candidates_length (F : Formula α) (z : ℕ → ℕ) (d : ℕ) :
    (candidates F z d).length =
      (dedupClauses F).length.choose (z d) * (coreCandidates F).length := by
  simp [candidates_eq, List.length_flatMap, List.length_sublistsLen]

/-- Candidate count, without treating list generation or literal comparison as free. -/
theorem candidates_length_le (F : Formula α) (z : ℕ → ℕ) (d k : ℕ)
    (hWidth : RawWidthAtMost k F) :
    (candidates F z d).length ≤ F.length ^ (z d + 1) * 2 ^ k := by
  rw [candidates_length]
  have hchoose : (dedupClauses F).length.choose (z d) ≤ F.length ^ z d :=
    (Nat.choose_le_pow _ _).trans
      (Nat.pow_le_pow_left (dedupClauses_length_le F) (z d))
  calc
    (dedupClauses F).length.choose (z d) * (coreCandidates F).length ≤
        F.length ^ z d * (F.length * 2 ^ k) :=
      Nat.mul_le_mul hchoose (coreCandidates_length_le F k hWidth)
    _ = F.length ^ (z d + 1) * 2 ^ k := by rw [pow_succ, Nat.mul_assoc]

/-- Actual predicate-test count is at most the generated candidate-list length. -/
theorem searchAt_count_le (F : Formula α) (z : ℕ → ℕ) (d : ℕ) :
    (searchAt F z d).2 ≤ (candidates F z d).length :=
  scan_count_le _ _

theorem searchAt_count_bound (F : Formula α) (z : ℕ → ℕ) (d k : ℕ)
    (hWidth : RawWidthAtMost k F) :
    (searchAt F z d).2 ≤ F.length ^ (z d + 1) * 2 ^ k :=
  (searchAt_count_le F z d).trans (candidates_length_le F z d k hWidth)

/-- Across all visited widths, count every complete Boolean candidate test. -/
theorem select_count_le (F : Formula α) (z : ℕ → ℕ) (k Z : ℕ)
    (hWidth : RawWidthAtMost k F)
    (hZ : ∀ d, 2 ≤ d → d ≤ k → z d ≤ Z) :
    (select F z k).2 ≤ k * ((F.length + 1) ^ (Z + 1) * 2 ^ k) := by
  have h := scanWidths_count_le (searchAt F z) 2 (k - 1)
    ((F.length + 1) ^ (Z + 1) * 2 ^ k) (by
      intro d hd hdk
      have hz := hZ d hd (by omega)
      apply (searchAt_count_bound F z d k hWidth).trans
      apply Nat.mul_le_mul_right
      exact (Nat.pow_le_pow_left (Nat.le_succ F.length) (z d + 1)).trans
        (Nat.pow_le_pow_right (by omega) (by omega)))
  exact h.trans (Nat.mul_le_mul_right _ (Nat.sub_le k 1))


/-- Polynomial structural-generation budget for fixed requested sunflower size. -/
def generationBudget (m k r : ℕ) : ℕ :=
  2 * (m + 1) ^ r + 2 * (m + 1) ^ (2 * r) +
    (m * (k + 2) + 1) + 3 * m * 2 ^ k +
    (m ^ r * (2 * (m * 2 ^ k) + 1) + 1)

theorem buildCandidates_count_le (F : Formula α) (z : ℕ → ℕ) (d k : ℕ)
    (hWidth : RawWidthAtMost k F) :
    (buildCandidates F z d).2 ≤ generationBudget F.length k (z d) := by
  let families := enumerateFixed (z d) (dedupClauses F)
  let cores := enumerateCoreFamily F
  have hbase : (dedupClauses F).length + 1 ≤ F.length + 1 :=
    Nat.add_le_add_right (dedupClauses_length_le F) 1
  have hcalls : families.calls ≤ 2 * (F.length + 1) ^ z d := by
    apply (Nat.le_succ _).trans
    exact (enumerateFixed_calls_le (z d) (dedupClauses F)).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase (z d)))
  have hcells : families.cells ≤ 2 * (F.length + 1) ^ (2 * z d) :=
    (enumerateFixed_cells_bound (z d) (dedupClauses F)).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbase (2 * z d)))
  have hcorecalls : cores.calls ≤ F.length * (k + 2) + 1 :=
    enumerateCoreFamily_calls_le F k hWidth
  have hcorecells : cores.cells ≤ 3 * F.length * 2 ^ k :=
    enumerateCoreFamily_cells_le F k hWidth
  have hfamlen : families.values.length ≤ F.length ^ z d := by
    rw [enumerateFixed_length]
    exact (Nat.choose_le_pow _ _).trans
      (Nat.pow_le_pow_left (dedupClauses_length_le F) (z d))
  have hcorelen : cores.values.length ≤ F.length * 2 ^ k :=
    coreCandidates_length_le F k hWidth
  have hpairs : (pairLists families.values cores.values).2 ≤
      F.length ^ z d * (2 * (F.length * 2 ^ k) + 1) + 1 := by
    rw [pairLists_count]
    apply Nat.add_le_add_right
    exact Nat.mul_le_mul hfamlen (by omega)
  change families.calls + families.cells + cores.calls + cores.cells +
    (pairLists families.values cores.values).2 ≤ _
  unfold generationBudget
  omega


/-- Every generated candidate has the bounded raw dimensions required by the
measured checker, whether or not it is a valid sunflower. -/
theorem candidate_bounds (F : Formula α) (z : ℕ → ℕ) (d k : ℕ)
    (hWidth : RawWidthAtMost k F) {c : Candidate α}
    (hc : c ∈ candidates F z d) :
    c.1.length = z d ∧ RawWidthAtMost k c.1 ∧ c.2.length ≤ k ∧
      c.1.length ≤ F.length ∧ (c.1.map clauseSet).Nodup := by
  rw [candidates_eq, enumerateFixed_values] at hc
  obtain ⟨G, hG, hpair⟩ := List.mem_flatMap.mp hc
  obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hpair
  obtain ⟨hGsub, hGlen⟩ := List.mem_sublistsLen.mp hG
  rw [coreCandidates, enumerateCoreFamily_values] at hH
  obtain ⟨C, hC, hHsub⟩ := List.mem_flatMap.mp hH
  have hHC := List.mem_sublists'.mp hHsub
  refine ⟨hGlen, ?_, hHC.length_le.trans (hWidth C hC),
    hGsub.length_le.trans (dedupClauses_length_le F), ?_⟩
  · intro D hD
    exact hWidth D (dedupClauses_subset F (hGsub.subset hD))
  · exact (dedupClauses_map_nodup F).sublist (hGsub.map clauseSet)

end SubexponentialSAT.ExecSunflowerSearch

end OAI.Algorithms
