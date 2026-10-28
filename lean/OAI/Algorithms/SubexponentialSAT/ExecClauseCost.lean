import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNF
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerSearch
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-!
# Explicit costs for the executable clause loops

These routines return their result together with the number of charged events
in the displayed recursive execution. A recursive list-case inspection costs
one event; a literal equality test costs one further event. These are list-loop
and comparison units, **not** primitive bit-machine transitions. In particular,
`DecidableEq α` is an equality interface, not a unit-cost bit implementation.
No cost is attached to an arbitrary uninstrumented function.
-/

namespace SubexponentialSAT.ExecClauseCost

universe u v
variable {α : Type u} {β : Type v}

abbrev Measured (α : Type u) := α × ℕ

/-- Instrumented membership: one list inspection and, for a cons, one equality. -/
def containsM [DecidableEq α] (x : α) : List α → Measured Bool
  | [] => (false, 1)
  | y :: ys =>
      if x = y then (true, 2)
      else let r := containsM x ys; (r.1, r.2 + 2)

/-- Instrumented short-circuit universal scan. -/
def allM (p : α → Measured Bool) : List α → Measured Bool
  | [] => (true, 1)
  | x :: xs =>
      let h := p x
      if h.1 then let r := allM p xs; (r.1, h.2 + r.2 + 1)
      else (false, h.2 + 1)

/-- Instrumented short-circuit existential scan. -/
def anyM (p : α → Measured Bool) : List α → Measured Bool
  | [] => (false, 1)
  | x :: xs =>
      let h := p x
      if h.1 then (true, h.2 + 1)
      else let r := anyM p xs; (r.1, h.2 + r.2 + 1)

/-- Instrumented filter; every list cell is visited exactly once by this loop. -/
def filterM (p : α → Measured Bool) : List α → Measured (List α)
  | [] => ([], 1)
  | x :: xs =>
      let h := p x
      let r := filterM p xs
      (if h.1 then x :: r.1 else r.1, h.2 + r.2 + 1)

/-- Length is computed recursively, rather than supplied as a free data query. -/
def lengthM : List α → Measured ℕ
  | [] => (0, 1)
  | _ :: xs => let r := lengthM xs; (r.1 + 1, r.2 + 1)

/-- Negation adds one Boolean operation. -/
def notM (p : Measured Bool) : Measured Bool := (!p.1, p.2 + 1)

/-- The second argument is delayed so the measured short circuit is real. -/
def andM (p : Measured Bool) (q : Unit → Measured Bool) : Measured Bool :=
  if p.1 then let r := q (); (r.1, p.2 + r.2 + 1)
  else (false, p.2 + 1)

/-- Delayed short-circuit disjunction. -/
def orM (p : Measured Bool) (q : Unit → Measured Bool) : Measured Bool :=
  if p.1 then (true, p.2 + 1)
  else let r := q (); (r.1, p.2 + r.2 + 1)

/-- Literal subset is an actual nested scan. -/
def subsetM [DecidableEq α] (C D : List α) : Measured Bool :=
  allM (fun x => containsM x D) C

def equivalentM [DecidableEq α] (C D : List α) : Measured Bool :=
  andM (subsetM C D) (fun _ => subsetM D C)

def strictSubsetM [DecidableEq α] (C D : List α) : Measured Bool :=
  andM (subsetM C D) (fun _ => notM (subsetM D C))

/-- Intersection implemented by filtering with membership tests. -/
def intersectionM [DecidableEq α] (C D : List α) : Measured (List α) :=
  filterM (fun x => containsM x D) C

@[simp] theorem allM_value (p : α → Measured Bool) (xs : List α) :
    (allM p xs).1 = xs.all (fun x => (p x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : (p x).1 <;> simp [allM, hp, ih]

@[simp] theorem anyM_value (p : α → Measured Bool) (xs : List α) :
    (anyM p xs).1 = xs.any (fun x => (p x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : (p x).1 <;> simp [anyM, hp, ih]

@[simp] theorem filterM_value (p : α → Measured Bool) (xs : List α) :
    (filterM p xs).1 = xs.filter (fun x => (p x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : (p x).1 <;> simp [filterM, hp, ih]

@[simp] theorem lengthM_value (xs : List α) : (lengthM xs).1 = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [lengthM, ih]

@[simp] theorem lengthM_cost (xs : List α) : (lengthM xs).2 = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [lengthM, ih]

@[simp] theorem notM_value (p : Measured Bool) : (notM p).1 = !p.1 := rfl

@[simp] theorem andM_value (p : Measured Bool) (q : Unit → Measured Bool) :
    (andM p q).1 = (p.1 && (q ()).1) := by
  cases hp : p.1 <;> simp [andM, hp]

@[simp] theorem orM_value (p : Measured Bool) (q : Unit → Measured Bool) :
    (orM p q).1 = (p.1 || (q ()).1) := by
  cases hp : p.1 <;> simp [orM, hp]

theorem andM_cost_le (p : Measured Bool) (q : Unit → Measured Bool) :
    (andM p q).2 ≤ p.2 + (q ()).2 + 1 := by
  cases hp : p.1 <;> simp [andM, hp]

theorem orM_cost_le (p : Measured Bool) (q : Unit → Measured Bool) :
    (orM p q).2 ≤ p.2 + (q ()).2 + 1 := by
  cases hp : p.1 <;> simp [orM, hp]

theorem allM_cost_le (p : α → Measured Bool) (xs : List α) (b : ℕ)
    (hp : ∀ x ∈ xs, (p x).2 ≤ b) : (allM p xs).2 ≤ xs.length * (b + 1) + 1 := by
  induction xs with
  | nil => simp [allM]
  | cons x xs ih =>
    have hx := hp x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hp y (List.mem_cons_of_mem x hy))
    have hs : (allM p (x :: xs)).2 ≤ (p x).2 + (allM p xs).2 + 1 := by
      cases h : (p x).1 <;> simp [allM, h]
    calc
      (allM p (x :: xs)).2 ≤ b + (xs.length * (b + 1) + 1) + 1 :=
        hs.trans (Nat.add_le_add_right (Nat.add_le_add hx ht) 1)
      _ = (x :: xs).length * (b + 1) + 1 := by simp [List.length_cons]; ring

theorem anyM_cost_le (p : α → Measured Bool) (xs : List α) (b : ℕ)
    (hp : ∀ x ∈ xs, (p x).2 ≤ b) : (anyM p xs).2 ≤ xs.length * (b + 1) + 1 := by
  induction xs with
  | nil => simp [anyM]
  | cons x xs ih =>
    have hx := hp x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hp y (List.mem_cons_of_mem x hy))
    have hs : (anyM p (x :: xs)).2 ≤ (p x).2 + (anyM p xs).2 + 1 := by
      cases h : (p x).1 <;> simp [anyM, h]
    calc
      (anyM p (x :: xs)).2 ≤ b + (xs.length * (b + 1) + 1) + 1 :=
        hs.trans (Nat.add_le_add_right (Nat.add_le_add hx ht) 1)
      _ = (x :: xs).length * (b + 1) + 1 := by simp [List.length_cons]; ring

theorem filterM_cost_le (p : α → Measured Bool) (xs : List α) (b : ℕ)
    (hp : ∀ x ∈ xs, (p x).2 ≤ b) : (filterM p xs).2 ≤ xs.length * (b + 1) + 1 := by
  induction xs with
  | nil => simp [filterM]
  | cons x xs ih =>
    have hx := hp x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hp y (List.mem_cons_of_mem x hy))
    calc
      (filterM p (x :: xs)).2 = (p x).2 + (filterM p xs).2 + 1 := rfl
      _ ≤ b + (xs.length * (b + 1) + 1) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add hx ht) 1
      _ = (x :: xs).length * (b + 1) + 1 := by simp [List.length_cons]; ring

theorem containsM_cost_le [DecidableEq α] (x : α) (xs : List α) :
    (containsM x xs).2 ≤ 2 * xs.length + 1 := by
  induction xs with
  | nil => simp [containsM]
  | cons y ys ih =>
    by_cases h : x = y
    · simp only [containsM, h, ↓reduceIte, List.length_cons]
      omega
    · simp only [containsM, h, ↓reduceIte, List.length_cons]
      omega

theorem subsetM_cost_le [DecidableEq α] (C D : List α) :
    (subsetM C D).2 ≤ C.length * (2 * D.length + 2) + 1 := by
  simpa [subsetM, Nat.add_assoc] using
    allM_cost_le (fun x => containsM x D) C (2 * D.length + 1)
      (fun x _ => containsM_cost_le x D)

theorem intersectionM_cost_le [DecidableEq α] (C D : List α) :
    (intersectionM C D).2 ≤ C.length * (2 * D.length + 2) + 1 := by
  simpa [intersectionM, Nat.add_assoc] using
    filterM_cost_le (fun x => containsM x D) C (2 * D.length + 1)
      (fun x _ => containsM_cost_le x D)

theorem equivalentM_cost_le [DecidableEq α] (C D : List α) :
    (equivalentM C D).2 ≤ 4 * (C.length + 1) * (D.length + 1) := by
  have h := andM_cost_le (subsetM C D) (fun _ => subsetM D C)
  have hc := subsetM_cost_le C D
  have hd := subsetM_cost_le D C
  have he : C.length * (2 * D.length + 2) + 1 +
      (D.length * (2 * C.length + 2) + 1) + 1 ≤
      4 * (C.length + 1) * (D.length + 1) := by
    nlinarith
  exact h.trans ((Nat.add_le_add_right (Nat.add_le_add hc hd) 1).trans he)

theorem strictSubsetM_cost_le [DecidableEq α] (C D : List α) :
    (strictSubsetM C D).2 ≤ 4 * (C.length + 1) * (D.length + 1) := by
  have h := andM_cost_le (subsetM C D) (fun _ => notM (subsetM D C))
  have hc := subsetM_cost_le C D
  have hd := subsetM_cost_le D C
  have he : C.length * (2 * D.length + 2) + 1 +
      ((D.length * (2 * C.length + 2) + 1) + 1) + 1 ≤
      4 * (C.length + 1) * (D.length + 1) := by
    nlinarith
  apply h.trans
  apply le_trans (Nat.add_le_add_right (Nat.add_le_add hc (Nat.add_le_add_right hd 1)) 1)
  exact he


section ExecutableBridge
variable [DecidableEq α]

@[simp] theorem containsM_value (x : α) (C : List α) :
    (containsM x C).1 = SubexponentialSAT.ExecCNF.contains x C := by
  induction C with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x = y <;> simp [containsM, SubexponentialSAT.ExecCNF.contains, h, ih]

@[simp] theorem subsetM_value (C D : List α) :
    (subsetM C D).1 = SubexponentialSAT.ExecCNF.subset C D := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
    simp only [subsetM, allM_value, List.all_cons, containsM_value,
      SubexponentialSAT.ExecCNF.subset]
    simpa only [subsetM, allM_value, containsM_value] using
      congrArg (fun b => SubexponentialSAT.ExecCNF.contains x D && b) ih

@[simp] theorem equivalentM_value (C D : List α) :
    (equivalentM C D).1 = SubexponentialSAT.ExecCNF.equivalent C D := by
  simp [equivalentM, SubexponentialSAT.ExecCNF.equivalent]

@[simp] theorem strictSubsetM_value (C D : List α) :
    (strictSubsetM C D).1 = SubexponentialSAT.ExecCNF.strictSubset C D := by
  simp [strictSubsetM, SubexponentialSAT.ExecCNF.strictSubset]

@[simp] theorem intersectionM_value (C D : List α) :
    (intersectionM C D).1 = C.filter (fun x => SubexponentialSAT.ExecCNF.contains x D) := by
  simp [intersectionM]

/-- The exact last-occurrence literal deduplication, with all comparisons charged. -/
def dedupLiteralsM : List α → Measured (List α)
  | [] => ([], 1)
  | x :: xs =>
      let h := containsM x xs
      let r := dedupLiteralsM xs
      (if h.1 then r.1 else x :: r.1, h.2 + r.2 + 1)

/-- The exact extensional clause deduplication, with its nested comparisons. -/
def dedupClausesM : List (List α) → Measured (List (List α))
  | [] => ([], 1)
  | C :: F =>
      let h := anyM (fun D => equivalentM C D) F
      let r := dedupClausesM F
      (if h.1 then r.1 else C :: r.1, h.2 + r.2 + 1)

@[simp] theorem dedupLiteralsM_value (C : List α) :
    (dedupLiteralsM C).1 = SubexponentialSAT.ExecCNF.dedupLiterals C := by
  induction C with
  | nil => rfl
  | cons x xs ih =>
    simp [dedupLiteralsM, SubexponentialSAT.ExecCNF.dedupLiterals, ih]

@[simp] theorem dedupClausesM_value (F : List (List α)) :
    (dedupClausesM F).1 = SubexponentialSAT.ExecCNF.dedupClauses F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simp [dedupClausesM, SubexponentialSAT.ExecCNF.dedupClauses, ih]

theorem dedupLiteralsM_cost_le (C : List α) :
    (dedupLiteralsM C).2 ≤ (C.length + 1) ^ 2 := by
  induction C with
  | nil => simp [dedupLiteralsM]
  | cons x xs ih =>
    have h := containsM_cost_le x xs
    change (containsM x xs).2 + (dedupLiteralsM xs).2 + 1 ≤ _
    simp only [List.length_cons]
    nlinarith

/-- A uniform concrete bound for comparing two width-bounded clauses. -/
def pairBudget (k : ℕ) : ℕ := 4 * (k + 1) * (k + 1)

theorem equivalentM_cost_le_width (C D : List α) {k : ℕ}
    (hC : C.length ≤ k) (hD : D.length ≤ k) :
    (equivalentM C D).2 ≤ pairBudget k := by
  apply (equivalentM_cost_le C D).trans
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.succ_le_succ hC))
    (Nat.succ_le_succ hD)

theorem strictSubsetM_cost_le_width (C D : List α) {k : ℕ}
    (hC : C.length ≤ k) (hD : D.length ≤ k) :
    (strictSubsetM C D).2 ≤ pairBudget k := by
  apply (strictSubsetM_cost_le C D).trans
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.succ_le_succ hC))
    (Nat.succ_le_succ hD)

/-- A useful invariant for executable (possibly not normalized) clause lists. -/
def WidthBound (k : ℕ) (F : List (List α)) : Prop := ∀ C ∈ F, C.length ≤ k

private theorem dedupClausesM_cost_aux (F : List (List α)) (k m : ℕ)
    (hwidth : WidthBound k F) (hlen : F.length ≤ m) :
    (dedupClausesM F).2 ≤ F.length * (m * (pairBudget k + 1) + 2) + 1 := by
  induction F with
  | nil => simp [dedupClausesM]
  | cons C F ih =>
    have hC := hwidth C (List.mem_cons_self ..)
    have hF : WidthBound k F := fun D hD => hwidth D (List.mem_cons_of_mem C hD)
    have hFm : F.length ≤ m := (Nat.le_succ _).trans hlen
    have ht := ih hF hFm
    have ha := anyM_cost_le (fun D => equivalentM C D) F (pairBudget k)
      (fun D hD => equivalentM_cost_le_width C D hC (hF D hD))
    have ha' : (anyM (fun D => equivalentM C D) F).2 ≤ m * (pairBudget k + 1) + 1 :=
      ha.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hFm) 1)
    change (anyM (fun D => equivalentM C D) F).2 + (dedupClausesM F).2 + 1 ≤ _
    calc
      _ ≤ (m * (pairBudget k + 1) + 1) +
          (F.length * (m * (pairBudget k + 1) + 2) + 1) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add ha' ht) 1
      _ = (C :: F).length * (m * (pairBudget k + 1) + 2) + 1 := by
        simp only [List.length_cons]
        ring

theorem dedupClausesM_cost_le (F : List (List α)) (k : ℕ)
    (hwidth : WidthBound k F) :
    (dedupClausesM F).2 ≤ F.length * (F.length * (pairBudget k + 1) + 2) + 1 :=
  dedupClausesM_cost_aux F k F.length hwidth le_rfl

theorem dedupClausesM_mem {C : List α} {F : List (List α)}
    (h : C ∈ (dedupClausesM F).1) : C ∈ F := by
  induction F with
  | nil => simp [dedupClausesM] at h
  | cons D F ih =>
    change C ∈ (if (anyM (fun E => equivalentM D E) F).1 then
      (dedupClausesM F).1 else D :: (dedupClausesM F).1) at h
    split at h
    · exact List.mem_cons_of_mem D (ih h)
    · rcases List.mem_cons.mp h with rfl | ht
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem D (ih ht)

theorem dedupClausesM_length_le (F : List (List α)) :
    (dedupClausesM F).1.length ≤ F.length := by
  rw [dedupClausesM_value]
  exact SubexponentialSAT.ExecCNF.dedupClauses_length_le F

/-- Explicit absorption: deduplicate, then scan all original clauses for each survivor. -/
def absorbM (F : List (List α)) : Measured (List (List α)) :=
  let distinct := dedupClausesM F
  let retained := filterM (fun C => notM (anyM (fun D => strictSubsetM D C) F)) distinct.1
  (retained.1, distinct.2 + retained.2 + 1)

theorem absorbM_cost_le (F : List (List α)) (k : ℕ) (hwidth : WidthBound k F) :
    (absorbM F).2 ≤ F.length * (2 * F.length * (pairBudget k + 1) + 5) + 3 := by
  have hd := dedupClausesM_cost_le F k hwidth
  have hc : ∀ C ∈ (dedupClausesM F).1,
      (notM (anyM (fun D => strictSubsetM D C) F)).2 ≤
        F.length * (pairBudget k + 1) + 2 := by
    intro C hC
    have hCw := hwidth C (dedupClausesM_mem hC)
    have ha := anyM_cost_le (fun D => strictSubsetM D C) F (pairBudget k)
      (fun D hD => strictSubsetM_cost_le_width D C (hwidth D hD) hCw)
    exact Nat.succ_le_succ ha
  have hf := filterM_cost_le (fun C => notM (anyM (fun D => strictSubsetM D C) F))
    (dedupClausesM F).1 (F.length * (pairBudget k + 1) + 2) hc
  have hf' : (filterM (fun C => notM (anyM (fun D => strictSubsetM D C) F))
      (dedupClausesM F).1).2 ≤
      F.length * (F.length * (pairBudget k + 1) + 3) + 1 :=
    hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (dedupClausesM_length_le F)) 1)
  change (dedupClausesM F).2 +
    (filterM (fun C => notM (anyM (fun D => strictSubsetM D C) F))
      (dedupClausesM F).1).2 + 1 ≤ _
  calc
    _ ≤ (F.length * (F.length * (pairBudget k + 1) + 2) + 1) +
        (F.length * (F.length * (pairBudget k + 1) + 3) + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add hd hf') 1
    _ = _ := by ring

end ExecutableBridge


/-- A structural equality scan of natural counters. This is a count of natural
constructor inspections, not a claim about a binary-number implementation. -/
def natEqM : ℕ → ℕ → Measured Bool
  | 0, 0 => (true, 1)
  | 0, _ + 1 => (false, 1)
  | _ + 1, 0 => (false, 1)
  | a + 1, b + 1 => let r := natEqM a b; (r.1, r.2 + 1)

@[simp] theorem natEqM_value (a b : ℕ) : (natEqM a b).1 = decide (a = b) := by
  induction a generalizing b with
  | zero => cases b <;> rfl
  | succ a ih => cases b <;> simp [natEqM, ih]

theorem natEqM_cost_le (a b : ℕ) : (natEqM a b).2 ≤ a + 1 := by
  induction a generalizing b with
  | zero => cases b <;> simp [natEqM]
  | succ a ih =>
    cases b with
    | zero => simp [natEqM]
    | succ b => simpa [natEqM] using Nat.succ_le_succ (ih b)

def isEmptyM : List α → Measured Bool
  | [] => (true, 1)
  | _ :: _ => (false, 1)

@[simp] theorem isEmptyM_value (xs : List α) : (isEmptyM xs).1 = xs.isEmpty := by
  cases xs <;> rfl

@[simp] theorem isEmptyM_cost (xs : List α) : (isEmptyM xs).2 = 1 := by
  cases xs <;> rfl

def lengthEqM (xs : List α) (n : ℕ) : Measured Bool :=
  let r := lengthM xs
  let t := natEqM r.1 n
  (t.1, r.2 + t.2 + 1)

@[simp] theorem lengthEqM_value (xs : List α) (n : ℕ) :
    (lengthEqM xs n).1 = decide (xs.length = n) := by simp [lengthEqM]

theorem lengthEqM_cost_le (xs : List α) (n : ℕ) :
    (lengthEqM xs n).2 ≤ 2 * xs.length + 3 := by
  have h := natEqM_cost_le xs.length n
  simp only [lengthEqM, lengthM_value, lengthM_cost]
  omega

theorem andM_cost_bound (p : Measured Bool) (q : Unit → Measured Bool)
    {a b : ℕ} (hp : p.2 ≤ a) (hq : (q ()).2 ≤ b) :
    (andM p q).2 ≤ a + b + 1 :=
  (andM_cost_le p q).trans (Nat.add_le_add_right (Nat.add_le_add hp hq) 1)

theorem orM_cost_bound (p : Measured Bool) (q : Unit → Measured Bool)
    {a b : ℕ} (hp : p.2 ≤ a) (hq : (q ()).2 ≤ b) :
    (orM p q).2 ≤ a + b + 1 :=
  (orM_cost_le p q).trans (Nat.add_le_add_right (Nat.add_le_add hp hq) 1)

section SunflowerChecker
variable [DecidableEq α]

def countDistinctM (G : List (List α)) (n : ℕ) : Measured Bool :=
  let r := dedupClausesM G
  let t := lengthEqM r.1 n
  (t.1, r.2 + t.2 + 1)

def widthEqM (C : List α) (d : ℕ) : Measured Bool :=
  let r := dedupLiteralsM C
  let t := lengthEqM r.1 d
  (t.1, r.2 + t.2 + 1)

def coreAndWidthM (H C : List α) (d : ℕ) : Measured Bool :=
  andM (subsetM H C) (fun _ => widthEqM C d)

def intersectionEqM (C D H : List α) : Measured Bool :=
  let r := intersectionM C D
  let t := equivalentM r.1 H
  (t.1, r.2 + t.2 + 1)

def pairCoreM (C D H : List α) : Measured Bool :=
  orM (equivalentM C D) (fun _ => intersectionEqM C D H)

/-- An instrumented implementation of the complete executable sunflower test. -/
def checkM (F : List (List α)) (z : ℕ → ℕ) (d : ℕ)
    (c : SubexponentialSAT.ExecSunflowerSearch.Candidate α) : Measured Bool :=
  andM
    (andM
      (andM
        (andM (allM (fun C => anyM (fun D => equivalentM C D) F) c.1)
          (fun _ => countDistinctM c.1 (z d)))
        (fun _ => notM (isEmptyM c.2)))
      (fun _ => allM (fun C => coreAndWidthM c.2 C d) c.1))
    (fun _ => allM (fun C => allM (fun D => pairCoreM C D c.2) c.1) c.1)

@[simp] theorem countDistinctM_value (G : List (List α)) (n : ℕ) :
    (countDistinctM G n).1 = decide ((SubexponentialSAT.ExecCNF.dedupClauses G).length = n) := by
  simp [countDistinctM]

@[simp] theorem widthEqM_value (C : List α) (d : ℕ) :
    (widthEqM C d).1 = decide ((SubexponentialSAT.ExecCNF.dedupLiterals C).length = d) := by
  simp [widthEqM]

@[simp] theorem checkM_value (F : List (List α)) (z : ℕ → ℕ) (d : ℕ)
    (c : SubexponentialSAT.ExecSunflowerSearch.Candidate α) :
    (checkM F z d c).1 = SubexponentialSAT.ExecSunflowerSearch.check F z d c := by
  simp [checkM, SubexponentialSAT.ExecSunflowerSearch.check, coreAndWidthM, pairCoreM,
    intersectionEqM, SubexponentialSAT.ExecSunflowerSearch.intersection]

/-- Explicit polynomial budgets. They count only events in the measured routines. -/
def countBudget (s k : ℕ) : ℕ := s * (s * (pairBudget k + 1) + 4) + 5

def widthBudget (k : ℕ) : ℕ := (k + 1) ^ 2 + 2 * k + 4

def coreWidthBudget (k : ℕ) : ℕ := k * (2 * k + 2) + widthBudget k + 2

def pairCoreBudget (k : ℕ) : ℕ := 2 * pairBudget k + k * (2 * k + 2) + 3

def checkerBudget (m s k : ℕ) : ℕ :=
  (s * (m * (pairBudget k + 1) + 2) + 1) + countBudget s k + 2 +
    (s * (coreWidthBudget k + 1) + 1) +
    (s * (s * (pairCoreBudget k + 1) + 2) + 1) + 4

theorem countDistinctM_cost_le (G : List (List α)) (n k : ℕ)
    (hwidth : WidthBound k G) : (countDistinctM G n).2 ≤ countBudget G.length k := by
  have hd := dedupClausesM_cost_le G k hwidth
  have ht := lengthEqM_cost_le (dedupClausesM G).1 n
  have hl := dedupClausesM_length_le G
  have ht' : (lengthEqM (dedupClausesM G).1 n).2 ≤ 2 * G.length + 3 :=
    ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hl) 3)
  change (dedupClausesM G).2 + (lengthEqM (dedupClausesM G).1 n).2 + 1 ≤ _
  calc
    _ ≤ (G.length * (G.length * (pairBudget k + 1) + 2) + 1) +
        (2 * G.length + 3) + 1 := Nat.add_le_add_right (Nat.add_le_add hd ht') 1
    _ = countBudget G.length k := by unfold countBudget; ring

theorem widthEqM_cost_le (C : List α) (d k : ℕ) (hC : C.length ≤ k) :
    (widthEqM C d).2 ≤ widthBudget k := by
  have hd := dedupLiteralsM_cost_le C
  have ht := lengthEqM_cost_le (dedupLiteralsM C).1 d
  have hl : (dedupLiteralsM C).1.length ≤ C.length := by
    rw [dedupLiteralsM_value]
    exact SubexponentialSAT.ExecCNF.dedupLiterals_length_le C
  have hdc : (dedupLiteralsM C).2 ≤ (k + 1) ^ 2 :=
    hd.trans (Nat.pow_le_pow_left (Nat.succ_le_succ hC) 2)
  have htc : (lengthEqM (dedupLiteralsM C).1 d).2 ≤ 2 * k + 3 :=
    ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hl.trans hC)) 3)
  exact Nat.add_le_add_right (Nat.add_le_add hdc htc) 1

theorem subsetM_cost_le_width (C D : List α) {k : ℕ}
    (hC : C.length ≤ k) (hD : D.length ≤ k) :
    (subsetM C D).2 ≤ k * (2 * k + 2) + 1 := by
  apply (subsetM_cost_le C D).trans
  exact Nat.add_le_add_right (Nat.mul_le_mul hC
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hD) 2)) 1

theorem intersectionM_cost_le_width (C D : List α) {k : ℕ}
    (hC : C.length ≤ k) (hD : D.length ≤ k) :
    (intersectionM C D).2 ≤ k * (2 * k + 2) + 1 := by
  apply (intersectionM_cost_le C D).trans
  exact Nat.add_le_add_right (Nat.mul_le_mul hC
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hD) 2)) 1

theorem coreAndWidthM_cost_le (H C : List α) (d k : ℕ)
    (hH : H.length ≤ k) (hC : C.length ≤ k) :
    (coreAndWidthM H C d).2 ≤ coreWidthBudget k := by
  have h := andM_cost_bound (subsetM H C) (fun _ => widthEqM C d)
    (subsetM_cost_le_width H C hH hC) (widthEqM_cost_le C d k hC)
  apply h.trans
  unfold coreWidthBudget
  omega

theorem pairCoreM_cost_le (C D H : List α) (k : ℕ)
    (hC : C.length ≤ k) (hD : D.length ≤ k) (hH : H.length ≤ k) :
    (pairCoreM C D H).2 ≤ pairCoreBudget k := by
  have hI : (intersectionM C D).1.length ≤ k := by
    rw [intersectionM_value]
    exact (List.length_filter_le _ _).trans hC
  have he := equivalentM_cost_le_width (intersectionM C D).1 H hI hH
  have hi := intersectionM_cost_le_width C D hC hD
  have hr : (intersectionEqM C D H).2 ≤ k * (2 * k + 2) + 1 + pairBudget k + 1 :=
    Nat.add_le_add_right (Nat.add_le_add hi he) 1
  have h := orM_cost_bound (equivalentM C D) (fun _ => intersectionEqM C D H)
    (equivalentM_cost_le_width C D hC hD) hr
  apply h.trans
  unfold pairCoreBudget
  omega

/-- Full checker work bounded from the actual nested list loops. -/
theorem checkM_cost_le (F : List (List α)) (z : ℕ → ℕ) (d : ℕ)
    (c : SubexponentialSAT.ExecSunflowerSearch.Candidate α) (k : ℕ)
    (hF : WidthBound k F) (hG : WidthBound k c.1) (hH : c.2.length ≤ k) :
    (checkM F z d c).2 ≤ checkerBudget F.length c.1.length k := by
  have hp := allM_cost_le (fun C => anyM (fun D => equivalentM C D) F) c.1
    (F.length * (pairBudget k + 1) + 1) (by
      intro C hC
      exact anyM_cost_le _ _ _ (fun D hD =>
        equivalentM_cost_le_width C D (hG C hC) (hF D hD)))
  have hc := countDistinctM_cost_le c.1 (z d) k hG
  have hn : (notM (isEmptyM c.2)).2 ≤ 2 := by simp [notM]
  have hw := allM_cost_le (fun C => coreAndWidthM c.2 C d) c.1 (coreWidthBudget k)
    (fun C hC => coreAndWidthM_cost_le c.2 C d k hH (hG C hC))
  have ht := allM_cost_le (fun C => allM (fun D => pairCoreM C D c.2) c.1) c.1
    (c.1.length * (pairCoreBudget k + 1) + 1) (by
      intro C hC
      exact allM_cost_le _ _ _ (fun D hD =>
        pairCoreM_cost_le C D c.2 k (hG C hC) (hG D hD) hH))
  have h1 := andM_cost_bound
    (allM (fun C => anyM (fun D => equivalentM C D) F) c.1)
    (fun _ => countDistinctM c.1 (z d)) hp hc
  have h2 := andM_cost_bound _ (fun _ => notM (isEmptyM c.2)) h1 hn
  have h3 := andM_cost_bound _
    (fun _ => allM (fun C => coreAndWidthM c.2 C d) c.1) h2 hw
  have h := andM_cost_bound _
    (fun _ => allM (fun C => allM (fun D => pairCoreM C D c.2) c.1) c.1) h3 ht
  apply h.trans
  unfold checkerBudget
  exact le_of_eq (by ring)

end SunflowerChecker


/-- Measured map counts each list-case inspection and callback event. -/
def mapM (p : α → Measured β) : List α → Measured (List β)
  | [] => ([], 1)
  | x :: xs =>
      let h := p x
      let r := mapM p xs
      (h.1 :: r.1, h.2 + r.2 + 1)

@[simp] theorem mapM_value (p : α → Measured β) (xs : List α) :
    (mapM p xs).1 = xs.map (fun x => (p x).1) := by
  induction xs <;> simp_all [mapM]

theorem mapM_cost_le (p : α → Measured β) (xs : List α) (b : ℕ)
    (hp : ∀ x ∈ xs, (p x).2 ≤ b) : (mapM p xs).2 ≤ xs.length * (b + 1) + 1 := by
  induction xs with
  | nil => simp [mapM]
  | cons x xs ih =>
    have hx := hp x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hp y (List.mem_cons_of_mem x hy))
    calc
      (mapM p (x :: xs)).2 = (p x).2 + (mapM p xs).2 + 1 := rfl
      _ ≤ b + (xs.length * (b + 1) + 1) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add hx ht) 1
      _ = (x :: xs).length * (b + 1) + 1 := by simp only [List.length_cons]; ring

def appendM : List α → List α → Measured (List α)
  | [], ys => (ys, 1)
  | x :: xs, ys => let r := appendM xs ys; (x :: r.1, r.2 + 1)

@[simp] theorem appendM_value (xs ys : List α) : (appendM xs ys).1 = xs ++ ys := by
  induction xs <;> simp_all [appendM]

@[simp] theorem appendM_cost (xs ys : List α) : (appendM xs ys).2 = xs.length + 1 := by
  induction xs <;> simp_all [appendM]

/-- First-match scan, charging each actual callback and each visited list case. -/
def scanM (p : α → Measured Bool) : List α → Measured (Option α)
  | [] => (none, 1)
  | x :: xs =>
      let h := p x
      if h.1 then (some x, h.2 + 1)
      else let r := scanM p xs; (r.1, h.2 + r.2 + 1)

@[simp] theorem scanM_value (p : α → Measured Bool) (xs : List α) :
    (scanM p xs).1 = (SubexponentialSAT.ExecSunflowerSearch.scan (fun x => (p x).1) xs).1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : (p x).1 <;> simp [scanM, SubexponentialSAT.ExecSunflowerSearch.scan, h, ih]

theorem scanM_cost_le (p : α → Measured Bool) (xs : List α) (b : ℕ)
    (hp : ∀ x ∈ xs, (p x).2 ≤ b) : (scanM p xs).2 ≤ xs.length * (b + 1) + 1 := by
  induction xs with
  | nil => simp [scanM]
  | cons x xs ih =>
    have hx := hp x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hp y (List.mem_cons_of_mem x hy))
    have hs : (scanM p (x :: xs)).2 ≤ (p x).2 + (scanM p xs).2 + 1 := by
      cases h : (p x).1 <;> simp [scanM, h]
    calc
      _ ≤ b + (xs.length * (b + 1) + 1) + 1 :=
        hs.trans (Nat.add_le_add_right (Nat.add_le_add hx ht) 1)
      _ = (x :: xs).length * (b + 1) + 1 := by simp only [List.length_cons]; ring

section Children
variable [DecidableEq α]

@[simp] theorem absorbM_value (F : List (List α)) :
    (absorbM F).1 = SubexponentialSAT.ExecCNF.absorb F := by
  simp [absorbM, SubexponentialSAT.ExecCNF.absorb]

def eraseClausesM (F S : List (List α)) : Measured (List (List α)) :=
  filterM (fun C => notM (anyM (fun D => equivalentM C D) S)) F

@[simp] theorem eraseClausesM_value (F S : List (List α)) :
    (eraseClausesM F S).1 = SubexponentialSAT.ExecCNF.eraseClauses F S := by
  simp [eraseClausesM, SubexponentialSAT.ExecCNF.eraseClauses]

def clausesM (H : List α) (P : List (List α)) : Measured (List (List α)) :=
  mapM (fun C => appendM H C) P

omit [DecidableEq α] in
@[simp] theorem clausesM_value (H : List α) (P : List (List α)) :
    (clausesM H P).1 = SubexponentialSAT.ExecCNF.clauses H P := by
  simp [clausesM, SubexponentialSAT.ExecCNF.clauses]

/-- Measured form of literal-list cleanup, before any tautology test. -/
def cleanLiteralsM (F : List (List α)) : Measured (List (List α)) :=
  mapM dedupLiteralsM F

@[simp] theorem cleanLiteralsM_value (F : List (List α)) :
    (cleanLiteralsM F).1 = F.map SubexponentialSAT.ExecCNF.dedupLiterals := by simp [cleanLiteralsM]

/-- All rebuilding, comparison, and absorption loops in the core child. -/
def childA_M (F : List (List α)) (H : List α) (P : List (List α)) :
    Measured (List (List α)) :=
  let selected := clausesM H P
  let remaining := eraseClausesM F selected.1
  let output := absorbM (H :: remaining.1)
  (output.1, selected.2 + remaining.2 + output.2 + 1)

/-- All rebuilding, comparison, append, and absorption loops in the petal child. -/
def childB_M (F : List (List α)) (H : List α) (P : List (List α)) :
    Measured (List (List α)) :=
  let selected := clausesM H P
  let remaining := eraseClausesM F selected.1
  let joined := appendM remaining.1 P
  let output := absorbM joined.1
  (output.1, selected.2 + remaining.2 + joined.2 + output.2 + 1)

@[simp] theorem childA_M_value (F : List (List α)) (H : List α) (P : List (List α)) :
    (childA_M F H P).1 = SubexponentialSAT.ExecCNF.childA F H P := by
  simp [childA_M, SubexponentialSAT.ExecCNF.childA]

@[simp] theorem childB_M_value (F : List (List α)) (H : List α) (P : List (List α)) :
    (childB_M F H P).1 = SubexponentialSAT.ExecCNF.childB F H P := by
  simp [childB_M, SubexponentialSAT.ExecCNF.childB]

omit [DecidableEq α] in
theorem clausesM_cost_le (H : List α) (P : List (List α)) :
    (clausesM H P).2 ≤ P.length * (H.length + 2) + 1 := by
  simpa [clausesM, Nat.add_assoc] using
    mapM_cost_le (fun C => appendM H C) P (H.length + 1) (by simp)

theorem cleanLiteralsM_cost_le (F : List (List α)) (k : ℕ) (hF : WidthBound k F) :
    (cleanLiteralsM F).2 ≤ F.length * ((k + 1)^2 + 1) + 1 := by
  apply mapM_cost_le
  intro C hC
  exact (dedupLiteralsM_cost_le C).trans
    (Nat.pow_le_pow_left (Nat.succ_le_succ (hF C hC)) 2)

theorem eraseClausesM_cost_le (F S : List (List α)) (k : ℕ)
    (hF : WidthBound k F) (hS : WidthBound k S) :
    (eraseClausesM F S).2 ≤ F.length * (S.length * (pairBudget k + 1) + 3) + 1 := by
  have h := filterM_cost_le
    (fun C => notM (anyM (fun D => equivalentM C D) S)) F
    (S.length * (pairBudget k + 1) + 2) (by
      intro C hC
      exact Nat.succ_le_succ (anyM_cost_le _ _ _ (fun D hD =>
        equivalentM_cost_le_width C D (hF C hC) (hS D hD))))
  simpa [eraseClausesM, Nat.add_assoc] using h

end Children

/-- The full checker budget is an explicit degree-four polynomial. -/
theorem checkerBudget_expansion (m s k : ℕ) :
    checkerBudget m s k = (4*k^2 + 8*k + 5)*m*s +
      (14*k^2 + 26*k + 17)*s^2 + (3*k^2 + 6*k + 16)*s + 14 := by
  unfold checkerBudget countBudget coreWidthBudget widthBudget pairCoreBudget pairBudget
  ring

theorem checkerBudget_mono_s (m k : ℕ) {s t : ℕ} (h : s ≤ t) :
    checkerBudget m s k ≤ checkerBudget m t k := by
  rw [checkerBudget_expansion, checkerBudget_expansion]
  gcongr


section LiteralNormalization
variable {V : Type u} [DecidableEq V]

/-- Negating a SAT literal changes its Boolean polarity; this is not an arbitrary
function with a supplied unit-cost annotation. -/
def oppositeContainsM (x : SubexponentialSAT.SAT.Literal V) (C : List (SubexponentialSAT.SAT.Literal V)) :
    Measured Bool :=
  let r := containsM ⟨x.variable, !x.positive⟩ C
  (r.1, r.2 + 1)

def tautologyLiteralM (C : List (SubexponentialSAT.SAT.Literal V)) : Measured Bool :=
  anyM (fun x => oppositeContainsM x C) C

def removeTautologiesLiteralM (F : List (List (SubexponentialSAT.SAT.Literal V))) :
    Measured (List (List (SubexponentialSAT.SAT.Literal V))) :=
  filterM (fun C => notM (tautologyLiteralM C)) F

def normalizeLiteralM (F : List (List (SubexponentialSAT.SAT.Literal V))) :
    Measured (List (List (SubexponentialSAT.SAT.Literal V))) :=
  let clean := cleanLiteralsM F
  let kept := removeTautologiesLiteralM clean.1
  let output := absorbM kept.1
  (output.1, clean.2 + kept.2 + output.2 + 1)

@[simp] theorem oppositeContainsM_value (x : SubexponentialSAT.SAT.Literal V)
    (C : List (SubexponentialSAT.SAT.Literal V)) :
    (oppositeContainsM x C).1 = SubexponentialSAT.ExecCNF.contains x.negate C := by
  simp [oppositeContainsM, SubexponentialSAT.SAT.Literal.negate]

@[simp] theorem tautologyLiteralM_value (C : List (SubexponentialSAT.SAT.Literal V)) :
    (tautologyLiteralM C).1 = SubexponentialSAT.ExecCNF.tautology SubexponentialSAT.SAT.Literal.negate C := by
  simp [tautologyLiteralM, SubexponentialSAT.ExecCNF.tautology]

@[simp] theorem removeTautologiesLiteralM_value (F : List (List (SubexponentialSAT.SAT.Literal V))) :
    (removeTautologiesLiteralM F).1 =
      SubexponentialSAT.ExecCNF.removeTautologies SubexponentialSAT.SAT.Literal.negate F := by
  simp [removeTautologiesLiteralM, SubexponentialSAT.ExecCNF.removeTautologies]

@[simp] theorem normalizeLiteralM_value (F : List (List (SubexponentialSAT.SAT.Literal V))) :
    (normalizeLiteralM F).1 = SubexponentialSAT.ExecCNF.normalize SubexponentialSAT.SAT.Literal.negate F := by
  simp [normalizeLiteralM, SubexponentialSAT.ExecCNF.normalize, SubexponentialSAT.ExecCNF.cleanLiterals]

theorem tautologyLiteralM_cost_le (C : List (SubexponentialSAT.SAT.Literal V)) :
    (tautologyLiteralM C).2 ≤ C.length * (2 * C.length + 3) + 1 := by
  have h := anyM_cost_le (fun x => oppositeContainsM x C) C (2 * C.length + 2) (by
    intro x hx
    exact Nat.succ_le_succ (containsM_cost_le ⟨x.variable, !x.positive⟩ C))
  simpa [tautologyLiteralM, Nat.add_assoc] using h

theorem removeTautologiesLiteralM_cost_le (F : List (List (SubexponentialSAT.SAT.Literal V)))
    (k : ℕ) (hF : WidthBound k F) :
    (removeTautologiesLiteralM F).2 ≤ F.length * (k * (2 * k + 3) + 3) + 1 := by
  have h := filterM_cost_le (fun C => notM (tautologyLiteralM C)) F
    (k * (2 * k + 3) + 2) (by
      intro C hC
      have hc := Nat.succ_le_succ (tautologyLiteralM_cost_le C)
      have hw := hF C hC
      have hg : C.length * (2 * C.length + 3) ≤ k * (2 * k + 3) := by gcongr
      exact hc.trans (by omega))
  simpa [removeTautologiesLiteralM, Nat.add_assoc] using h

/-- An explicit event polynomial for input normalization. -/
def normalizationBudget (m k : ℕ) : ℕ :=
  (m * ((k + 1)^2 + 1) + 1) +
  (m * (k * (2 * k + 3) + 3) + 1) +
  (m * (2 * m * (pairBudget k + 1) + 5) + 3) + 1

theorem normalizeLiteralM_cost_le (F : List (List (SubexponentialSAT.SAT.Literal V)))
    (k : ℕ) (hF : WidthBound k F) :
    (normalizeLiteralM F).2 ≤ normalizationBudget F.length k := by
  have hc := cleanLiteralsM_cost_le F k hF
  have hcw : WidthBound k (cleanLiteralsM F).1 := by
    intro C hC
    rw [cleanLiteralsM_value] at hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    exact (SubexponentialSAT.ExecCNF.dedupLiterals_length_le D).trans (hF D hD)
  have hcl : (cleanLiteralsM F).1.length = F.length := by simp
  have ht := removeTautologiesLiteralM_cost_le (cleanLiteralsM F).1 k hcw
  rw [hcl] at ht
  have htw : WidthBound k (removeTautologiesLiteralM (cleanLiteralsM F).1).1 := by
    intro C hC
    rw [removeTautologiesLiteralM_value] at hC
    exact hcw C (List.mem_filter.mp hC).1
  have htl : (removeTautologiesLiteralM (cleanLiteralsM F).1).1.length ≤ F.length := by
    rw [removeTautologiesLiteralM_value]
    exact (SubexponentialSAT.ExecCNF.removeTautologies_length_le _ _).trans hcl.le
  have ha := absorbM_cost_le (removeTautologiesLiteralM (cleanLiteralsM F).1).1 k htw
  have ha' : (absorbM (removeTautologiesLiteralM (cleanLiteralsM F).1).1).2 ≤
      F.length * (2 * F.length * (pairBudget k + 1) + 5) + 3 := by
    apply ha.trans
    gcongr
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc ht) ha') 1

end LiteralNormalization

/-- On generated candidates, selected clauses are a sublist of the input. The
checker cost is therefore quadratic in input clause count and fixed width. -/
theorem checkerBudget_le_quadratic (m s k : ℕ) (hs : s ≤ m) :
    checkerBudget m s k ≤ 64 * (m + 1)^2 * (k + 1)^2 := by
  have ha : 4*k^2 + 8*k + 5 ≤ 5*(k+1)^2 := by nlinarith
  have hb : 14*k^2 + 26*k + 17 ≤ 17*(k+1)^2 := by nlinarith
  have hc : 3*k^2 + 6*k + 16 ≤ 16*(k+1)^2 := by nlinarith
  have hd : 1 ≤ (k+1)^2 := by nlinarith
  rw [checkerBudget_expansion]
  calc
    _ ≤ (5*(k+1)^2)*m*m + (17*(k+1)^2)*m^2 + (16*(k+1)^2)*m + 14*(k+1)^2 := by
      gcongr; nlinarith
    _ = (22*m^2 + 16*m + 14)*(k+1)^2 := by ring
    _ ≤ 64*(m+1)^2*(k+1)^2 := by gcongr; nlinarith

open SubexponentialSAT.BitProgram

/-- Fixed finite code comparing two bit strings destructively. Register 4 is the answer. -/
abbrev bitEqualityProgram : Program 5 2 10 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .pop 1 2 3 2
    | 2 => .bxor 4 1 3 3
    | 3 => .branch 4 8 4
    | 4 => .branch 1 5 7
    | 5 => .bxor 4 0 2 6
    | 6 => .branch 4 8 0
    | 7 => .set 4 true 9
    | 8 => .set 4 false 9
    | _ => .halt

def bitStacks (xs ys : List Bool) : Fin 2 → List Bool :=
  fun i => if i = 0 then xs else ys

def bitEqualityStart (r : Fin 5 → Bool) (xs ys : List Bool) : Cfg 5 2 10 :=
  ⟨some 0, r, bitStacks xs ys⟩

def poppedRegs (r : Fin 5 → Bool) (x y : Option Bool) : Fin 5 → Bool :=
  readRegs (readRegs r 0 1 x) 2 3 y

def bitEqualityEnd (r : Fin 5 → Bool) (xs ys : List Bool) (answer : Bool) : Cfg 5 2 10 :=
  ⟨none, Function.update r 4 answer, bitStacks xs ys⟩

theorem bitStacks_pop_left (xs ys : List Bool) :
    Function.update (bitStacks xs ys) 0 xs.tail = bitStacks xs.tail ys := by
  funext i
  fin_cases i <;> simp [bitStacks]

theorem bitStacks_pop_right (xs ys : List Bool) :
    Function.update (bitStacks xs ys) 1 ys.tail = bitStacks xs ys.tail := by
  funext i
  fin_cases i <;> simp [bitStacks]

theorem bitEquality_nil_nil (r : Fin 5 → Bool) :
    Trace bitEqualityProgram 7 (bitEqualityStart r [] [])
      (bitEqualityEnd (poppedRegs r none none) [] [] true) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, bitEqualityProgram, execInstr,
    bitEqualityStart, bitEqualityEnd, poppedRegs, readRegs, bitStacks]
  funext i
  fin_cases i <;> simp [bitStacks]

theorem bitEquality_cons_nil (r : Fin 5 → Bool) (x : Bool) (xs : List Bool) :
    Trace bitEqualityProgram 6 (bitEqualityStart r (x :: xs) [])
      (bitEqualityEnd (poppedRegs r (some x) none) xs [] false) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, bitEqualityProgram, execInstr,
    bitEqualityStart, bitEqualityEnd, poppedRegs, readRegs, bitStacks]
  funext i
  fin_cases i <;> simp [bitStacks]

theorem bitEquality_nil_cons (r : Fin 5 → Bool) (y : Bool) (ys : List Bool) :
    Trace bitEqualityProgram 6 (bitEqualityStart r [] (y :: ys))
      (bitEqualityEnd (poppedRegs r none (some y)) [] ys false) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, bitEqualityProgram, execInstr,
    bitEqualityStart, bitEqualityEnd, poppedRegs, readRegs, bitStacks]
  funext i
  fin_cases i <;> simp [bitStacks]

theorem bitEquality_cons_eq (r : Fin 5 → Bool) (x : Bool) (xs ys : List Bool) :
    Trace bitEqualityProgram 7 (bitEqualityStart r (x :: xs) (x :: ys))
      (bitEqualityStart (Function.update (poppedRegs r (some x) (some x)) 4 false) xs ys) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, bitEqualityProgram, execInstr,
    bitEqualityStart, poppedRegs, readRegs, bitStacks]
  funext i
  fin_cases i <;> simp [bitStacks]

theorem bitEquality_cons_ne (r : Fin 5 → Bool) (x y : Bool) (xs ys : List Bool)
    (h : x ≠ y) :
    Trace bitEqualityProgram 9 (bitEqualityStart r (x :: xs) (y :: ys))
      (bitEqualityEnd (poppedRegs r (some x) (some y)) xs ys false) := by
  have hxor : (x ^^ y) = true := by cases x <;> cases y <;> simp_all
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, bitEqualityProgram, execInstr,
    bitEqualityStart, bitEqualityEnd, poppedRegs, readRegs, bitStacks, hxor]
  funext i
  fin_cases i <;> simp [bitStacks]


/-- A genuine instruction trace. Comparison destroys the inspected prefixes;
it may leave residual tails on an early mismatch. -/
theorem bitEquality_runs (r : Fin 5 → Bool) (xs ys : List Bool) :
    ∃ n ≤ 9 * (xs.length + 1), ∃ c : Cfg 5 2 10,
      Trace bitEqualityProgram n (bitEqualityStart r xs ys) c ∧
      c.pc = none ∧ c.regs 4 = decide (xs = ys) := by
  induction xs generalizing r ys with
  | nil =>
    cases ys with
    | nil =>
      refine ⟨7, by simp, bitEqualityEnd (poppedRegs r none none) [] [] true,
        bitEquality_nil_nil r, rfl, ?_⟩
      simp [bitEqualityEnd]
    | cons y ys =>
      refine ⟨6, by simp, bitEqualityEnd (poppedRegs r none (some y)) [] ys false,
        bitEquality_nil_cons r y ys, rfl, ?_⟩
      simp [bitEqualityEnd]
  | cons x xs ih =>
    cases ys with
    | nil =>
      refine ⟨6, by simp; omega,
        bitEqualityEnd (poppedRegs r (some x) none) xs [] false,
        bitEquality_cons_nil r x xs, rfl, ?_⟩
      simp [bitEqualityEnd]
    | cons y ys =>
      by_cases hxy : x = y
      · subst y
        obtain ⟨n, hn, c, hc, hpc, hout⟩ :=
          ih (Function.update (poppedRegs r (some x) (some x)) 4 false) ys
        refine ⟨7 + n, ?_, c, (bitEquality_cons_eq r x xs ys).trans hc, hpc, ?_⟩
        · simp only [List.length_cons]
          omega
        · simpa using hout
      · refine ⟨9, by simp,
          bitEqualityEnd (poppedRegs r (some x) (some y)) xs ys false,
          bitEquality_cons_ne r x y xs ys hxy, rfl, ?_⟩
        simp [bitEqualityEnd, hxy]

theorem bitEquality_runsIn (r : Fin 5 → Bool) (xs ys : List Bool) :
    ∃ c : Cfg 5 2 10,
      RunsIn bitEqualityProgram (9 * (xs.length + 1)) (bitEqualityStart r xs ys) c ∧
      c.pc = none ∧ c.regs 4 = decide (xs = ys) := by
  obtain ⟨n, hn, c, hc, hpc, hout⟩ := bitEquality_runs r xs ys
  exact ⟨c, ⟨n, hn, hc⟩, hpc, hout⟩


theorem bitEquality_step_length_le {c c' : Cfg 5 2 10}
    (h : step bitEqualityProgram c = some c') (i : Fin 2) :
    (c'.stacks i).length ≤ (c.stacks i).length := by
  cases hpc : c.pc with
  | none => simp [step, hpc] at h
  | some q =>
    have he : execInstr (bitEqualityProgram.code q) c = c' := by
      simpa [step, hpc] using h
    subst c'
    fin_cases q <;> simp [ execInstr]
    all_goals
      simp only [Function.update_apply]
      split <;> simp_all [List.length_tail]

theorem bitEquality_trace_length_le {c c' : Cfg 5 2 10} {n : ℕ}
    (h : Trace bitEqualityProgram n c c') (i : Fin 2) :
    (c'.stacks i).length ≤ (c.stacks i).length := by
  induction h with
  | refl => exact le_rfl
  | cons hs ht ih => exact ih.trans (bitEquality_step_length_le hs i)

/-- The additional size postcondition permits the caller to charge cleanup. -/
theorem bitEquality_runsIn_bounded (r : Fin 5 → Bool) (xs ys : List Bool) :
    ∃ c : Cfg 5 2 10,
      RunsIn bitEqualityProgram (9 * (xs.length + 1)) (bitEqualityStart r xs ys) c ∧
      c.pc = none ∧ c.regs 4 = decide (xs = ys) ∧
      (c.stacks 0).length ≤ xs.length ∧ (c.stacks 1).length ≤ ys.length := by
  obtain ⟨c, ⟨n, hn, ht⟩, hpc, hout⟩ := bitEquality_runsIn r xs ys
  refine ⟨c, ⟨n, hn, ht⟩, hpc, hout, ?_, ?_⟩
  · simpa [bitEqualityStart, bitStacks] using bitEquality_trace_length_le ht 0
  · simpa [bitEqualityStart, bitStacks] using bitEquality_trace_length_le ht 1


/-- A real primitive-bit-machine execution from an encoded two-stack comparison
boundary. This is deliberately not a claim about raw one-stack SAT input. -/
theorem bitEquality_primitive_runs (r : Fin 5 → Bool) (xs ys : List Bool) :
    ∃ c : Cfg 5 2 10,
      SubexponentialSAT.Computation.RunsIn
        (SubexponentialSAT.BitProgram.primitive bitEqualityProgram).step
        (SubexponentialSAT.BitProgram.primitiveOverhead bitEqualityProgram *
          (9 * (xs.length + 1)))
        (SubexponentialSAT.BitProgram.primitiveCfg bitEqualityProgram (bitEqualityStart r xs ys))
        (SubexponentialSAT.BitProgram.primitiveCfg bitEqualityProgram c) ∧
      c.pc = none ∧ c.regs 4 = decide (xs = ys) ∧
      (c.stacks 0).length ≤ xs.length ∧ (c.stacks 1).length ≤ ys.length := by
  obtain ⟨c, hc, hpc, hout, hleft, hright⟩ := bitEquality_runsIn_bounded r xs ys
  exact ⟨c, SubexponentialSAT.BitProgram.primitive_execution bitEqualityProgram hc,
    hpc, hout, hleft, hright⟩



section ChildCostBounds
variable [DecidableEq α]

/-- A common explicit event budget for either concrete sunflower child. -/
def childBudget (m s k : ℕ) : ℕ :=
  (s * (k + 2) + 1) +
  (m * (s * (pairBudget (2*k) + 1) + 3) + 1) + (m + 1) +
  ((m+s+1) * (2*(m+s+1)*(pairBudget (2*k)+1)+5)+3) + 1

theorem child_preparation_bounds (F : List (List α)) (H : List α) (P : List (List α))
    (k : ℕ) (hF : WidthBound k F) (hH : H.length ≤ k) (hP : WidthBound k P) :
    (clausesM H P).2 ≤ P.length * (k+2)+1 ∧
    (eraseClausesM F (clausesM H P).1).2 ≤
      F.length * (P.length * (pairBudget (2*k)+1)+3)+1 ∧
    WidthBound (2*k) (eraseClausesM F (clausesM H P).1).1 ∧
    (eraseClausesM F (clausesM H P).1).1.length ≤ F.length := by
  have hFw : WidthBound (2*k) F := by
    intro C hC
    have := hF C hC
    omega
  have hSw : WidthBound (2*k) (clausesM H P).1 := by
    intro C hC
    rw [clausesM_value] at hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
    have := hP D hD
    simp only [List.length_append]
    omega
  have hSl : (clausesM H P).1.length = P.length := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (clausesM_cost_le H P).trans
    gcongr
  · simpa only [hSl] using eraseClausesM_cost_le F (clausesM H P).1 (2*k) hFw hSw
  · intro C hC
    rw [eraseClausesM_value] at hC
    exact hFw C (List.mem_filter.mp hC).1
  · rw [eraseClausesM_value]
    exact SubexponentialSAT.ExecCNF.eraseClauses_length_le _ _

theorem childA_M_cost_le (F : List (List α)) (H : List α) (P : List (List α))
    (k : ℕ) (hF : WidthBound k F) (hH : H.length ≤ k) (hP : WidthBound k P) :
    (childA_M F H P).2 ≤ childBudget F.length P.length k := by
  obtain ⟨hs, he, hrw, hrl⟩ := child_preparation_bounds F H P k hF hH hP
  have hw : WidthBound (2*k) (H :: (eraseClausesM F (clausesM H P).1).1) := by
    intro C hC
    rcases List.mem_cons.mp hC with rfl | hC
    · omega
    · exact hrw C hC
  have hl : (H :: (eraseClausesM F (clausesM H P).1).1).length ≤
      F.length + P.length + 1 := by simp only [List.length_cons]; omega
  have ha := absorbM_cost_le (H :: (eraseClausesM F (clausesM H P).1).1) (2*k) hw
  have ha' : (absorbM (H :: (eraseClausesM F (clausesM H P).1).1)).2 ≤
      (F.length+P.length+1) *
        (2*(F.length+P.length+1)*(pairBudget (2*k)+1)+5)+3 := by
    apply ha.trans
    gcongr
  change (clausesM H P).2 + (eraseClausesM F (clausesM H P).1).2 +
    (absorbM (H :: (eraseClausesM F (clausesM H P).1).1)).2 + 1 ≤ _
  apply (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hs he) ha') 1).trans
  unfold childBudget
  omega

theorem childB_M_cost_le (F : List (List α)) (H : List α) (P : List (List α))
    (k : ℕ) (hF : WidthBound k F) (hH : H.length ≤ k) (hP : WidthBound k P) :
    (childB_M F H P).2 ≤ childBudget F.length P.length k := by
  obtain ⟨hs, he, hrw, hrl⟩ := child_preparation_bounds F H P k hF hH hP
  have hw : WidthBound (2*k) ((eraseClausesM F (clausesM H P).1).1 ++ P) := by
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · exact hrw C hC
    · have := hP C hC
      omega
  have hl : ((eraseClausesM F (clausesM H P).1).1 ++ P).length ≤
      F.length + P.length + 1 := by simp only [List.length_append]; omega
  have ha := absorbM_cost_le ((eraseClausesM F (clausesM H P).1).1 ++ P) (2*k) hw
  have ha' : (absorbM ((eraseClausesM F (clausesM H P).1).1 ++ P)).2 ≤
      (F.length+P.length+1) *
        (2*(F.length+P.length+1)*(pairBudget (2*k)+1)+5)+3 := by
    apply ha.trans
    gcongr
  have hj : (appendM (eraseClausesM F (clausesM H P).1).1 P).2 ≤ F.length+1 := by
    rw [appendM_cost]
    omega
  simp only [childB_M, appendM_value]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hs he) hj) ha') 1


end ChildCostBounds

theorem succ_le_power_of_two_le (b e : ℕ) (hb : 2 ≤ b) : e + 1 ≤ b ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    calc
      e + 1 + 1 ≤ 2 * (e + 1) := by omega
      _ ≤ 2 * b^e := Nat.mul_le_mul_left 2 ih
      _ ≤ b * b^e := Nat.mul_le_mul_right _ hb
      _ = b^(e+1) := by rw [pow_succ]; ring

/-- The full checker is polynomial in the variable count after normalized-clause
cardinality is supplied. This bounds measured events, not primitive bit steps. -/
theorem checkerBudget_le_variable_power (n m s k : ℕ)
    (hn : 1 ≤ n) (hm : m ≤ (2*n+1)^k) (hs : s ≤ m) :
    checkerBudget m s k ≤ (n+1)^(6*k+8) := by
  have hb : 2 ≤ n+1 := by omega
  have hbase : 2*n+1 ≤ (n+1)^2 := by nlinarith
  have hm' : m ≤ (n+1)^(2*k) := by
    calc
      m ≤ (2*n+1)^k := hm
      _ ≤ ((n+1)^2)^k := Nat.pow_le_pow_left hbase k
      _ = (n+1)^(2*k) := by rw [pow_mul]
  have hp : 0 < (n+1)^(2*k) := pow_pos (by omega) _
  have hmp : m+1 ≤ (n+1)^(2*k+1) := by
    calc
      m+1 ≤ 2*(n+1)^(2*k) := by omega
      _ ≤ (n+1)*(n+1)^(2*k) := Nat.mul_le_mul_right _ hb
      _ = (n+1)^(2*k+1) := by rw [pow_succ]; ring
  have hkp := succ_le_power_of_two_le (n+1) k hb
  have hc : 64 ≤ (n+1)^6 := by
    exact Nat.pow_le_pow_left hb 6
  apply (checkerBudget_le_quadratic m s k hs).trans
  calc
    64*(m+1)^2*(k+1)^2 ≤ (n+1)^6*((n+1)^(2*k+1))^2*((n+1)^k)^2 := by gcongr
    _ = (n+1)^(6*k+8) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring

theorem checkM_cost_le_variable_power {α : Type*} [DecidableEq α]
    (F : List (List α)) (z : ℕ → ℕ) (d : ℕ)
    (c : SubexponentialSAT.ExecSunflowerSearch.Candidate α) (n k : ℕ)
    (hn : 1 ≤ n) (hm : F.length ≤ (2*n+1)^k)
    (hs : c.1.length ≤ F.length) (hF : WidthBound k F)
    (hG : WidthBound k c.1) (hH : c.2.length ≤ k) :
    (checkM F z d c).2 ≤ (n+1)^(6*k+8) :=
  (checkM_cost_le F z d c k hF hG hH).trans
    (checkerBudget_le_variable_power n F.length c.1.length k hn hm hs)


end SubexponentialSAT.ExecClauseCost

end OAI.Algorithms
