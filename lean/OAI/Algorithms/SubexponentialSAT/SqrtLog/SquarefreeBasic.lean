import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! Sparse squarefree polynomials. The index monoid multiplies by support union,
so the coefficient algebra imposes X_v^2 = X_v without enumerating all supports. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

variable {V R : Type*}

/-- A type tag prevents the support-union multiplication leaking to all finsets. -/
structure Support (V : Type*) where
  vars : Finset V
  deriving DecidableEq

@[ext] theorem Support.ext {a b : Support V} (h : a.vars = b.vars) : a = b := by
  cases a; cases b; cases h; rfl

instance [DecidableEq V] : CommMonoid (Support V) where
  one := ⟨∅⟩
  mul a b := ⟨a.vars ∪ b.vars⟩
  mul_assoc a b c := Support.ext (Finset.union_assoc _ _ _)
  one_mul a := Support.ext (Finset.empty_union _)
  mul_one a := Support.ext (Finset.union_empty _)
  mul_comm a b := Support.ext (Finset.union_comm _ _)

@[simp] theorem vars_one [DecidableEq V] : (1 : Support V).vars = ∅ := rfl
@[simp] theorem vars_mul [DecidableEq V] (a b : Support V) :
    (a * b).vars = a.vars ∪ b.vars := rfl

@[simp] theorem support_mul_eq [DecidableEq V] (a b : Support V) (s : Finset V) :
    a * b = Support.mk s ↔ a.vars ∪ b.vars = s := by
  constructor
  · intro h; exact congrArg Support.vars h
  · exact Support.ext

abbrev Poly (V R : Type*) [Semiring R] := MonoidAlgebra R (Support V)

noncomputable section

variable [DecidableEq V] [CommSemiring R]

def monomial (s : Finset V) (c : R) : Poly V R := MonoidAlgebra.single ⟨s⟩ c

def coeff (s : Finset V) (f : Poly V R) : R := f.coeff ⟨s⟩

def coeffHom (s : Finset V) : Poly V R →+ R where
  toFun := coeff s
  map_zero' := rfl
  map_add' _ _ := rfl

def scalar : R →+* Poly V R := MonoidAlgebra.singleOneRingHom

@[simp] theorem coeff_scalar_mul (s : Finset V) (c : R) (f : Poly V R) :
    coeff s (scalar c * f) = c * coeff s f := by
  exact MonoidAlgebra.coeff_single_one_mul f c (Support.mk s)

@[simp] theorem coeff_zero (s : Finset V) : coeff s (0 : Poly V R) = 0 := rfl
@[simp] theorem coeff_add (s : Finset V) (f g : Poly V R) :
    coeff s (f + g) = coeff s f + coeff s g := rfl
@[simp] theorem coeff_monomial (s t : Finset V) (c : R) :
    coeff s (monomial t c) = if t = s then c else 0 := by
  by_cases h : t = s
  · subst s
    simp [coeff, monomial]
  · have hs : Support.mk t ≠ Support.mk s := fun e => h (congrArg Support.vars e)
    simp [coeff, monomial, h, hs]

@[simp] theorem monomial_mul (s t : Finset V) (a b : R) :
    monomial s a * monomial t b = monomial (s ∪ t) (a * b) := by
  change MonoidAlgebra.single (Support.mk s) a * MonoidAlgebra.single (Support.mk t) b =
    MonoidAlgebra.single (Support.mk (s ∪ t)) (a * b)
  rw [MonoidAlgebra.single_mul_single]
  congr

theorem coeff_mul (s : Finset V) (f g : Poly V R) :
    coeff s (f * g) = f.coeff.sum (fun a c => g.coeff.sum (fun b d =>
      if a.vars ∪ b.vars = s then c * d else 0)) := by
  simpa [coeff, Support.mk.injEq] using MonoidAlgebra.coeff_mul f g ⟨s⟩

def weight (x : V → R) (s : Finset V) : R := ∏ v ∈ s, x v

private theorem mul_weight_of_mem (x : V → R) (hx : ∀ v, x v * x v = x v)
    (s : Finset V) {v : V} (hv : v ∈ s) : x v * weight x s = weight x s := by
  rw [weight, ← Finset.insert_erase hv, Finset.prod_insert (Finset.notMem_erase _ _)]
  rw [← mul_assoc, hx]

theorem weight_union (x : V → R) (hx : ∀ v, x v * x v = x v)
    (s t : Finset V) : weight x (s ∪ t) = weight x s * weight x t := by
  induction s using Finset.induction_on with
  | empty => simp [weight]
  | @insert v s hv ih =>
      by_cases hvt : v ∈ t
      · rw [Finset.insert_union, Finset.insert_eq_of_mem (Finset.mem_union_right _ hvt)]
        have hins : weight x (insert v s) = x v * weight x s := by
          simp [weight, hv]
        rw [hins]
        rw [ih, mul_assoc, mul_left_comm (x v), mul_weight_of_mem x hx t hvt]
      · rw [Finset.insert_union]
        rw [weight, Finset.prod_insert (by simp [hv, hvt])]
        change x v * weight x (s ∪ t) = weight x (insert v s) * weight x t
        have hins : weight x (insert v s) = x v * weight x s := by
          simp [weight, hv]
        rw [ih, hins, mul_assoc]

def weightHom (x : V → R) (hx : ∀ v, x v * x v = x v) : Support V →* R where
  toFun s := weight x s.vars
  map_one' := by simp [weight]
  map_mul' a b := weight_union x hx a.vars b.vars

/-- Evaluation at idempotent values is a ring/semiring homomorphism. -/
def evalHom (x : V → R) (hx : ∀ v, x v * x v = x v) : Poly V R →+* R :=
  MonoidAlgebra.liftNCRingHom (RingHom.id R) (weightHom x hx)
    (fun a b => Commute.all a ((weightHom x hx) b))

@[simp] theorem eval_monomial (x : V → R) (hx : ∀ v, x v * x v = x v)
    (s : Finset V) (c : R) : evalHom x hx (monomial s c) = c * weight x s := by
  exact MonoidAlgebra.liftNC_single _ _ _ _

theorem eval_eq_sum (x : V → R) (hx : ∀ v, x v * x v = x v) (f : Poly V R) :
    evalHom x hx f = f.coeff.sum (fun s c => c * weight x s.vars) := by
  calc
    evalHom x hx f = evalHom x hx (f.coeff.sum MonoidAlgebra.single) := by
      rw [MonoidAlgebra.sum_coeff_single]
    _ = f.coeff.sum (fun s c => c * weight x s.vars) := by
      rw [map_finsuppSum]
      apply Finsupp.sum_congr
      intro a ha
      exact eval_monomial x hx a.vars (f.coeff a)

def boolValue (x : V → Bool) (v : V) : R := if x v then 1 else 0

omit [DecidableEq V] in
theorem boolValue_idempotent (x : V → Bool) (v : V) :
    boolValue (R := R) x v * boolValue x v = boolValue x v := by
  cases h : x v <;> simp [boolValue, h]

def evalBool (x : V → Bool) : Poly V R →+* R := evalHom (boolValue x) (boolValue_idempotent x)

/-- A support-cardinality bound, with no finiteness assumption on the ambient variables. -/
def Bounded (d : ℕ) (f : Poly V R) : Prop :=
  ∀ s ∈ f.coeff.support, s.vars.card ≤ d

theorem bounded_zero (d : ℕ) : Bounded d (0 : Poly V R) := by simp [Bounded]

omit [DecidableEq V] in
theorem Bounded.mono {d e : ℕ} {f : Poly V R} (h : Bounded d f) (he : d ≤ e) :
    Bounded e f := fun s hs => (h s hs).trans he

omit [DecidableEq V] in
theorem bounded_monomial (s : Finset V) (c : R) {d : ℕ} (h : s.card ≤ d) :
    Bounded d (monomial s c) := by
  intro a ha
  have : a = Support.mk s := Finset.mem_singleton.mp (Finsupp.support_single_subset ha)
  subst a
  exact h

theorem bounded_one : Bounded 0 (1 : Poly V R) := bounded_monomial ∅ 1 (by simp)

theorem Bounded.add {d : ℕ} {f g : Poly V R} (hf : Bounded d f) (hg : Bounded d g) :
    Bounded d (f + g) := by
  intro a ha
  rcases Finset.mem_union.mp (Finsupp.support_add ha) with h | h
  · exact hf a h
  · exact hg a h

theorem Bounded.mul {d e : ℕ} {f g : Poly V R} (hf : Bounded d f) (hg : Bounded e g) :
    Bounded (d + e) (f * g) := by
  intro a ha
  have hmem := MonoidAlgebra.support_coeff_mul_subset f g ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_image₂.mp hmem
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hf b hb) (hg c hc))

theorem bounded_sum {ι : Type*} (s : Finset ι) (f : ι → Poly V R) (d : ℕ)
    (h : ∀ i ∈ s, Bounded d (f i)) : Bounded d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_zero (V := V) (R := R) d
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
