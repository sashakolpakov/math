import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Explicit finite list loops for head moments

The callbacks are the concrete bounded squarefree operations, not a source
evaluation oracle. The code computes every recursive result once. The cost
theorems charge every callback invocation; representation-specific costs are
substituted after the normalized-list size bound is proved.
-/

namespace SubexponentialSAT.SqrtLog.MomentsAlgorithm

structure Ops (R I E : Type*) where
  zero : E
  one : E
  add : E → E → E × ℕ
  mul : E → E → E × ℕ
  scale : R → E → E × ℕ
  project : I → E → E × ℕ

variable {R I E : Type*}

/-- One actual head bucket, with one scalar weight and one stored local jet
per assignment. No global assignment tuple is enumerated. -/
def head (op : Ops R I E) : List (R × E) → E × ℕ
  | [] => (op.zero, 0)
  | a :: l =>
      let term := op.scale a.1 a.2
      let tail := head op l
      let joined := op.add term.1 tail.1
      (joined.1, term.2 + tail.2 + joined.2)

/-- Multiply the independently computed head moments. -/
def heads (op : Ops R I E) : List (List (R × E)) → E × ℕ
  | [] => (op.one, 0)
  | l :: ls =>
      let term := head op l
      let tail := heads op ls
      let joined := op.mul term.1 tail.1
      (joined.1, term.2 + tail.2 + joined.2)

/-- Evaluate every retained support, extract it, and sum its contribution. -/
def run (op : Ops R I E) (data : I → List (List (R × E))) : List I → E × ℕ
  | [] => (op.zero, 0)
  | i :: is =>
      let product := heads op (data i)
      let term := op.project i product.1
      let tail := run op data is
      let joined := op.add term.1 tail.1
      (joined.1, product.2 + term.2 + tail.2 + joined.2)

section Correctness

variable {A : Type*} [CommSemiring R] [CommSemiring A]

structure Correct (op : Ops R I E) (denote : E → A)
    (scalar : R →+* A) (project : I → A → A) : Prop where
  zero : denote op.zero = 0
  one : denote op.one = 1
  add : ∀ a b, denote (op.add a b).1 = denote a + denote b
  mul : ∀ a b, denote (op.mul a b).1 = denote a * denote b
  scale : ∀ c a, denote (op.scale c a).1 = scalar c * denote a
  project : ∀ i a, denote (op.project i a).1 = project i (denote a)

theorem head_correct (op : Ops R I E) (denote : E → A)
    (scalar : R →+* A) (project : I → A → A)
    (h : Correct op denote scalar project) (l : List (R × E)) :
    denote (head op l).1 = (l.map fun a => scalar a.1 * denote a.2).sum := by
  induction l with
  | nil => exact h.zero
  | cons a l ih =>
      simpa only [head, List.map_cons, List.sum_cons] using
        (h.add (op.scale a.1 a.2).1 (head op l).1).trans
          (by rw [h.scale, ih])

theorem heads_correct (op : Ops R I E) (denote : E → A)
    (scalar : R →+* A) (project : I → A → A)
    (h : Correct op denote scalar project) (ls : List (List (R × E))) :
    denote (heads op ls).1 =
      (ls.map fun l => (l.map fun a => scalar a.1 * denote a.2).sum).prod := by
  induction ls with
  | nil => exact h.one
  | cons l ls ih =>
      simp only [heads, List.map_cons, List.prod_cons]
      rw [h.mul, head_correct op denote scalar project h, ih]

theorem run_correct (op : Ops R I E) (denote : E → A)
    (scalar : R →+* A) (project : I → A → A)
    (h : Correct op denote scalar project)
    (data : I → List (List (R × E))) (is : List I) :
    denote (run op data is).1 =
      (is.map fun i => project i
        ((data i).map fun l => (l.map fun a => scalar a.1 * denote a.2).sum).prod).sum := by
  induction is with
  | nil => exact h.zero
  | cons i is ih =>
      simp only [run, List.map_cons, List.sum_cons]
      rw [h.add, h.project, heads_correct op denote scalar project h, ih]

end Correctness

section Costs

def entries (ls : List (List (R × E))) : ℕ := (ls.map List.length).sum

variable (op : Ops R I E) (ca cm cs cp : ℕ)
  (ha : ∀ a b, (op.add a b).2 ≤ ca)
  (hm : ∀ a b, (op.mul a b).2 ≤ cm)
  (hs : ∀ c a, (op.scale c a).2 ≤ cs)
  (hp : ∀ i a, (op.project i a).2 ≤ cp)

include ha hs in
theorem head_cost (l : List (R × E)) :
    (head op l).2 ≤ l.length * (cs + ca) := by
  induction l with
  | nil => simp [head]
  | cons a l ih =>
      have h1 := hs a.1 a.2
      have h2 := ha (op.scale a.1 a.2).1 (head op l).1
      simp only [head, List.length_cons]
      calc
        _ ≤ cs + l.length * (cs + ca) + ca := by omega
        _ = (l.length + 1) * (cs + ca) := by ring

include ha hm hs in
theorem heads_cost (ls : List (List (R × E))) :
    (heads op ls).2 ≤ entries ls * (cs + ca) + ls.length * cm := by
  induction ls with
  | nil => simp [heads, entries]
  | cons l ls ih =>
      have h1 := head_cost op ca cs ha hs l
      have h2 := hm (head op l).1 (heads op ls).1
      simp only [heads, entries, List.map_cons, List.sum_cons, List.length_cons] at *
      calc
        _ ≤ l.length * (cs + ca) +
          ((ls.map List.length).sum * (cs + ca) + ls.length * cm) + cm := by omega
        _ = (l.length + (ls.map List.length).sum) * (cs + ca) +
          (ls.length + 1) * cm := by ring

def budget (data : I → List (List (R × E))) (is : List I)
    (ca cm cs cp : ℕ) : ℕ :=
  (is.map fun i => entries (data i) * (cs + ca) + (data i).length * cm + cp + ca).sum

include ha hm hs hp in
theorem run_cost (data : I → List (List (R × E))) (is : List I) :
    (run op data is).2 ≤ budget data is ca cm cs cp := by
  induction is with
  | nil => simp [run, budget]
  | cons i is ih =>
      have h1 := heads_cost op ca cm cs ha hm hs (data i)
      have h2 := hp i (heads op (data i)).1
      have h3 := ha (op.project i (heads op (data i)).1).1 (run op data is).1
      simp only [run, budget, List.map_cons, List.sum_cons] at *
      omega

/- Substituting bounded squarefree callback costs gives a fixed polynomial
in the support count, times the actual head enumeration. -/
include ha hm hs hp in
theorem run_cost_uniform (data : I → List (List (R × E))) (is : List I)
    (N H : ℕ) (hN : ∀ i ∈ is, entries (data i) ≤ N)
    (hH : ∀ i ∈ is, (data i).length ≤ H) :
    (run op data is).2 ≤ is.length * (N * (cs + ca) + H * cm + cp + ca) := by
  refine (run_cost op ca cm cs cp ha hm hs hp data is).trans ?_
  unfold budget
  induction is with
  | nil => simp
  | cons i is ih =>
      have hNi := hN i (by simp)
      have hHi := hH i (by simp)
      have htail := ih (fun j hj => hN j (by simp [hj]))
        (fun j hj => hH j (by simp [hj]))
      have h1 := Nat.mul_le_mul_right (cs + ca) hNi
      have h2 := Nat.mul_le_mul_right cm hHi
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        _ ≤ (N * (cs + ca) + H * cm + cp + ca) +
          is.length * (N * (cs + ca) + H * cm + cp + ca) := by omega
        _ = (is.length + 1) * (N * (cs + ca) + H * cm + cp + ca) := by ring

end Costs

end SubexponentialSAT.SqrtLog.MomentsAlgorithm

end OAI.Algorithms
