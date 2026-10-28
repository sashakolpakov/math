import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAlgorithm
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeJet

namespace OAI.Algorithms

/-! Exact semantics for the concrete loops when multiplication clips U and Z.
The normal form is additive but is not falsely treated as a ring homomorphism.
Every intermediate clipping is justified by the two-sided product identity. -/

namespace SubexponentialSAT.SqrtLog.MomentsAlgorithm

variable {R I E A : Type*} [CommSemiring R] [CommSemiring A]

structure CanonicalCorrect (op : Ops R I E) (denote : E → A)
    (scalar : R →+* A) (project : I → A → A) (norm : A →+ A) : Prop where
  idempotent : ∀ a, norm (norm a) = norm a
  mul_normal : ∀ a b, norm (norm a * norm b) = norm (a * b)
  project_normal : ∀ i a, norm (project i (norm a)) = norm (project i a)
  zero : denote op.zero = 0
  one : denote op.one = norm 1
  add : ∀ a b, denote (op.add a b).1 = norm (denote a + denote b)
  mul : ∀ a b, denote (op.mul a b).1 = norm (denote a * denote b)
  scale : ∀ c a, denote (op.scale c a).1 = norm (scalar c * denote a)
  project : ∀ i a, denote (op.project i a).1 = norm (project i (denote a))

theorem head_canonical (op : Ops R I E) (denote : E → A)
    (scalar : R →+* A) (project : I → A → A) (norm : A →+ A)
    (h : CanonicalCorrect op denote scalar project norm) (l : List (R × E)) :
    denote (head op l).1 = norm ((l.map fun a => scalar a.1 * denote a.2).sum) := by
  induction l with
  | nil => simpa [head] using h.zero
  | cons a l ih =>
      simp only [head, List.map_cons, List.sum_cons]
      rw [h.add, h.scale, ih]
      simp only [map_add, h.idempotent]

theorem heads_canonical (op : Ops R I E) (denote : E → A)
    (scalar : R →+* A) (project : I → A → A) (norm : A →+ A)
    (h : CanonicalCorrect op denote scalar project norm) (ls : List (List (R × E))) :
    denote (heads op ls).1 = norm
      ((ls.map fun l => (l.map fun a => scalar a.1 * denote a.2).sum).prod) := by
  induction ls with
  | nil => exact h.one
  | cons l ls ih =>
      simp only [heads, List.map_cons, List.prod_cons]
      rw [h.mul, head_canonical op denote scalar project norm h, ih, h.mul_normal]

theorem run_canonical (op : Ops R I E) (denote : E → A)
    (scalar : R →+* A) (project : I → A → A) (norm : A →+ A)
    (h : CanonicalCorrect op denote scalar project norm)
    (data : I → List (List (R × E))) (is : List I) :
    denote (run op data is).1 = norm
      ((is.map fun i => project i
        ((data i).map fun l => (l.map fun a => scalar a.1 * denote a.2).sum).prod).sum) := by
  induction is with
  | nil => simpa [run] using h.zero
  | cons i is ih =>
      simp only [run, List.map_cons, List.sum_cons]
      rw [h.add, h.project, heads_canonical op denote scalar project norm h, ih]
      simp only [map_add, h.idempotent, h.project_normal]


end SubexponentialSAT.SqrtLog.MomentsAlgorithm

namespace SubexponentialSAT.SqrtLog.Moments

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

/-- The two actual truncations are idempotent, coefficient by coefficient. -/
theorem canonical_idempotent (t J : ℕ) (a : Squarefree.Jet V R) :
    Squarefree.canonical t J (Squarefree.canonical t J a) = Squarefree.canonical t J a := by
  ext u z
  by_cases h : u < t ∧ z < J <;> simp [Squarefree.coeff_canonical, h]


theorem canonical_mul_left (t J : ℕ) (a b : Squarefree.Jet V R) :
    Squarefree.canonical t J (Squarefree.canonical t J a * b) =
      Squarefree.canonical t J (a * b) := by
  calc
    _ = Squarefree.canonical t J
        (Squarefree.canonical t J (Squarefree.canonical t J a) * Squarefree.canonical t J b) :=
      (Squarefree.canonical_mul t J (Squarefree.canonical t J a) b).symm
    _ = _ := by rw [canonical_idempotent, Squarefree.canonical_mul]

theorem canonical_mul_right (t J : ℕ) (a b : Squarefree.Jet V R) :
    Squarefree.canonical t J (a * Squarefree.canonical t J b) =
      Squarefree.canonical t J (a * b) := by
  rw [mul_comm a (Squarefree.canonical t J b), canonical_mul_left, mul_comm b a]

theorem canonical_list_prod (t J : ℕ) (l : List (Squarefree.Jet V R)) :
    Squarefree.canonical t J ((l.map (Squarefree.canonical t J)).prod) =
      Squarefree.canonical t J l.prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [canonical_mul_left]
      calc
        _ = Squarefree.canonical t J (a * Squarefree.canonical t J
            ((l.map (Squarefree.canonical t J)).prod)) := (canonical_mul_right _ _ _ _).symm
        _ = _ := by rw [ih, canonical_mul_right]

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
