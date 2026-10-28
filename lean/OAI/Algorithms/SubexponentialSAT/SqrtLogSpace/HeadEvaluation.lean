import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsBuckets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutInterface
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsSparse
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Restricted sums over the actual Boolean heads. All products are formed in
one coefficient ring before any additive coefficient readout. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments

/-- An actual head rescan tests the entire key and the correction predicate.
The finite sum here specifies its result; it does not materialize a fiber. -/
theorem fiber_sum_eq_rescan {X K R : Type*} [Fintype X] [DecidableEq K]
    [AddCommMonoid R] (label : X → K) (key : K) (P : X → Prop)
    [DecidablePred P] (f : X → R) :
    (∑ a : {x // label x = key}, if P a.val then f a.val else 0) =
      ∑ a : X, if label a = key ∧ P a then f a else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x => label x = key))
    (by simp) (fun x => if P x then f x else 0), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hk : label x = key <;> simp [hk]

section RestrictedSeparation

variable {R G : Type*} {X : G → Type*} [CommSemiring R]
  [Fintype G] [DecidableEq G] [∀ g, Fintype (X g)]

/-- Representatives belong to their signature fibers but need not satisfy
any of the additional local correction restrictions. -/
theorem restricted_separation (reps : ∀ g, X g)
    (A : G → (∀ g, X g) → R) (P : ∀ g, X g → Prop)
    [∀ g, DecidablePred (P g)]
    (hA : ∀ g x y, x g = y g → A g x = A g y) :
    (∑ x : ∀ g, X g, if ∀ g, P g (x g) then ∏ g, A g x else 0) =
      ∏ g, ∑ a : X g, if P g a then A g (Function.update reps g a) else 0 := by
  have h := OAI.Algorithms.SubexponentialSAT.SubexpSeparation.weighted_separation reps A
    (fun x => if ∀ g, P g (x g) then 1 else 0) 1
    (fun g a => if P g a then 1 else 0) hA
    (fun x => by simp only [one_mul, Fintype.prod_boole])
  simpa only [one_mul, ite_mul, zero_mul] using h

end RestrictedSeparation

section LayoutLocality

variable {V I F G O B R : Type*} [Fintype V] [DecidableEq V]
  [Fintype F] [Fintype G] [DecidableEq G] [CommRing O] [Add B] [CommMonoid R]
variable {owner : I → V} {factor : I → F} {Q d : ℕ}

/-- Immediate Boolean specialization makes the correction independent of the
summation assignment. Every factor still reads the one shared original row. -/
theorem corrected_group_locality
    (L : OAI.Algorithms.SubexponentialSAT.SqrtLog.Layout.Data (O := O) (G := G) owner factor Q d)
    (t : Fin Q) (g : G) (lift : O → B) (correction : I → B)
    (evaluate : ∀ f : F, ({i : I // factor i = f} → B) → R)
    (x z : V → ℤ) (hown : L.restrict t g x = L.restrict t g z)
    (hother : ∀ h, h ≠ g → L.bucketLabel t h (L.restrict t h x) =
      L.bucketLabel t h (L.restrict t h z)) :
    (∏ f : {f : F // L.color f t = g},
      evaluate f.val (fun i => lift (L.nodeValue t i.val x) + correction i.val)) =
    ∏ f : {f : F // L.color f t = g},
      evaluate f.val (fun i => lift (L.nodeValue t i.val z) + correction i.val) := by
  apply Finset.prod_congr rfl
  intro f _
  apply congrArg (evaluate f.val)
  funext i
  apply congrArg (fun a => lift a + correction i.val)
  have hf : L.color (factor i.val) t = g :=
    (congrArg (fun f => L.color f t) i.property).trans f.property
  apply L.nodeValue_eq_of_buckets t i.val x z
  · rw [hf]
    exact hown
  · intro h hh
    exact hother h (by simpa only [hf] using hh)

end LayoutLocality

section BooleanHeads

variable {V G R : Type*} [Fintype V] [Fintype G]
  [DecidableEq V] [DecidableEq G] [CommSemiring R]
variable {L : G → Type*} [∀ g, DecidableEq (L g)]

omit [Fintype V] [Fintype G] [DecidableEq V] [DecidableEq G] in
/-- The current finite-difference support restricts original variables.
There is one Boolean choice per variable, including variables with no incidences. -/
theorem restricted_assemble_iff (head : V → G) (E : Finset V)
    (a : ∀ g, Head head g → Bool) :
    (∀ v ∈ E, assemble head a v = true) ↔
      ∀ g (v : Head head g), v.val ∈ E → a g v = true := by
  constructor
  · intro h g v hv
    rcases v with ⟨v, hg⟩
    cases hg
    exact h v hv
  · intro h v hv
    exact h (head v) ⟨v, rfl⟩ hv

/-- Reindex by attained full labels and perform each restricted head sum.
`hA` is the locality proved from the actual layout's integer kernels. -/
theorem restricted_grouping (head : V → G)
    (label : ∀ g, (Head head g → Bool) → L g)
    (reps : ∀ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g))
    (E : Finset V) (A : G → (V → Bool) → R)
    (hA : ∀ g x z, split head x g = split head z g →
      (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
      A g x = A g z) :
    (∑ x : V → Bool, if ∀ v ∈ E, x v = true then ∏ g, A g x else 0) =
      ∑ y : ∀ g, LabelValue label g, ∏ g,
        ∑ a : LabelBucket label g (y g),
          if ∀ v : Head head g, v.val ∈ E → a.val v = true then
            A g (assemble head (fun h =>
              (Function.update (reps y) g a h).val)) else 0 := by
  classical
  rw [sum_boolean_actual_buckets head label]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [restricted_assemble_iff]
  apply restricted_separation (reps y)
    (fun g x => A g (assemble head (fun h => (x h).val)))
    (fun g a => ∀ v : Head head g, v.val ∈ E → a.val v = true)
  intro g x z hxz
  apply hA g
  · have hx := (headEquiv head).apply_symm_apply (fun h => (x h).val)
    have hz := (headEquiv head).apply_symm_apply (fun h => (z h).val)
    change split head (assemble head (fun h => (x h).val)) = _ at hx
    change split head (assemble head (fun h => (z h).val)) = _ at hz
    rw [hx, hz]
    exact congrArg Subtype.val hxz
  · intro h _
    have hx := (headEquiv head).apply_symm_apply (fun h => (x h).val)
    have hz := (headEquiv head).apply_symm_apply (fun h => (z h).val)
    change split head (assemble head (fun h => (x h).val)) = _ at hx
    change split head (assemble head (fun h => (z h).val)) = _ at hz
    rw [hx, hz, (x h).property, (z h).property]

end BooleanHeads

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

variable {V R : Type*} [DecidableEq V]

def specializeEntries (U : Finset V) : List (Squarefree.Index V × R) →
    List (Squarefree.Index V × R)
  | [] => []
  | (a,c)::xs => if a.vars ⊆ U then (⟨a.u,a.z,∅⟩,c)::specializeEntries U xs
      else specializeEntries U xs

theorem specializeEntries_length (U : Finset V) (xs : List (Squarefree.Index V × R)) :
    (specializeEntries U xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [specializeEntries]
  | cons a xs ih =>
    rcases a with ⟨a,c⟩
    by_cases h : a.vars ⊆ U <;> simp [specializeEntries,h] <;> omega

theorem specializeEntries_empty (U : Finset V) (xs : List (Squarefree.Index V × R))
    (a : Squarefree.Index V × R) (ha : a ∈ specializeEntries U xs) : a.1.vars = ∅ := by
  induction xs with
  | nil => simp [specializeEntries] at ha
  | cons b xs ih =>
    rcases b with ⟨b,c⟩
    by_cases h : b.vars ⊆ U
    · simp only [specializeEntries,h,ite_true,List.mem_cons] at ha
      rcases ha with rfl | ha
      · rfl
      · exact ih ha
    · simp only [specializeEntries,h,ite_false] at ha
      exact ih ha

theorem mem_specializeEntries (U : Finset V) (xs : List (Squarefree.Index V × R))
    (b : Squarefree.Index V × R) (hb : b ∈ specializeEntries U xs) :
    ∃ a ∈ xs, a.1.vars ⊆ U ∧ b = (⟨a.1.u,a.1.z,∅⟩,a.2) := by
  induction xs with
  | nil => simp [specializeEntries] at hb
  | cons a xs ih =>
    by_cases h : a.1.vars ⊆ U
    · simp only [specializeEntries, h, ite_true, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨a,List.mem_cons_self,h,rfl⟩
      · obtain ⟨c,hc,hU,he⟩ := ih hb
        exact ⟨c,List.mem_cons_of_mem a hc,hU,he⟩
    · simp only [specializeEntries, h, ite_false] at hb
      obtain ⟨c,hc,hU,he⟩ := ih hb
      exact ⟨c,List.mem_cons_of_mem a hc,hU,he⟩

theorem specializeEntries_map {S : Type*} (U : Finset V)
    (xs : List (Squarefree.Index V × R)) (f : R → S) :
    specializeEntries U (xs.map (fun a => (a.1,f a.2))) =
      (specializeEntries U xs).map (fun a => (a.1,f a.2)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a.1.vars ⊆ U <;> simp [specializeEntries,h,ih]

variable [CommSemiring R]

omit [CommSemiring R] in
/-- Specialization may collide keys, so validity is proved before normalization;
no false uniqueness assumption is made about the filtered list. -/
theorem specializeEntries_valid (U vars : Finset V) (t J : ℕ)
    (xs : List (Squarefree.Index V × R))
    (h : Squarefree.Sparse.ValidData vars t J xs) :
    Squarefree.Sparse.ValidData ∅ t J (specializeEntries U xs) := by
  intro k hk
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hk
  obtain ⟨a,ha,_,rfl⟩ := mem_specializeEntries U xs b hb
  have ha' := h a.1 (List.mem_map.mpr ⟨a,ha,rfl⟩)
  exact ⟨ha'.1,by simp [Squarefree.Index.Valid],Finset.Subset.refl ∅⟩

theorem subset_weight (U E : Finset V) :
    Squarefree.weight (fun v => if v ∈ U then (1:R) else 0) E =
      if E ⊆ U then 1 else 0 := by
  simp only [Squarefree.weight, Finset.prod_boole, Finset.subset_iff]

theorem specialize_atom (U : Finset V) (a : Squarefree.Index V) (c : R) :
    Moments.jetScalar (V := V) (Moments.jetEval (fun v => if v ∈ U then (1:R) else 0)
      (by intro v; split <;> simp) (Squarefree.Sparse.atom a c)) =
      if a.vars ⊆ U then Squarefree.Sparse.atom ⟨a.u,a.z,∅⟩ c else 0 := by
  simp only [Moments.jetScalar,Moments.jetEval,Polynomial.coe_mapRingHom,
    Squarefree.Sparse.atom,Polynomial.map_monomial,Squarefree.eval_monomial]
  rw [subset_weight]
  split <;> simp [Squarefree.scalar,Squarefree.monomial,show (1 : Squarefree.Support V) = ⟨∅⟩ from rfl]

theorem specializeEntries_denote (U : Finset V) (xs : List (Squarefree.Index V × R)) :
    Squarefree.Sparse.denote (specializeEntries U xs) =
      Moments.jetScalar (V := V) (Moments.jetEval (fun v => if v ∈ U then (1:R) else 0)
        (by intro v; split <;> simp) (Squarefree.Sparse.denote xs)) := by
  induction xs with
  | nil => simp [specializeEntries,Squarefree.Sparse.denote,Squarefree.Sparse.decode]
  | cons a xs ih =>
    rcases a with ⟨a,c⟩
    change Squarefree.Sparse.denote (if a.vars ⊆ U then _ else _) = _
    simp only [Squarefree.Sparse.denote,Squarefree.Sparse.decode,map_add,specialize_atom]
    by_cases h : a.vars ⊆ U <;> simp [h,Squarefree.Sparse.decode,ih,Squarefree.Sparse.denote]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments

variable {V G R : Type*} [Fintype V] [Fintype G]
  [DecidableEq V] [DecidableEq G] [CommSemiring R]
variable {L : G → Type*} [∀ g, DecidableEq (L g)]

/-- Each attained tuple is followed by one bounded-width raw head rescan;
the complete key is checked before a contribution is admitted. -/
theorem restricted_grouping_rescan (head : V → G)
    (label : ∀ g, (Head head g → Bool) → L g)
    (reps : ∀ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g))
    (E : Finset V) (A : G → (V → Bool) → R)
    (hA : ∀ g x z, split head x g = split head z g →
      (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
      A g x = A g z) :
    (∑ x : V → Bool, if ∀ v ∈ E, x v = true then ∏ g, A g x else 0) =
      ∑ y : ∀ g, LabelValue label g, ∏ g,
        ∑ a : Head head g → Bool,
          if label g a = (y g).val ∧ (∀ v : Head head g, v.val ∈ E → a v=true) then
            A g (assemble head (Function.update (fun h => (reps y h).val) g a)) else 0 := by
  classical
  rw [restricted_grouping head label reps E A hA]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro g _
  rw [←fiber_sum_eq_rescan (label g) (y g).val
    (fun a => ∀ v : Head head g, v.val ∈ E → a v=true)
    (fun a => A g (assemble head (Function.update (fun h => (reps y h).val) g a)))]
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  apply congrArg (assemble head)
  funext h
  by_cases hh : h=g
  · subst h
    simp
  · simp [Function.update_of_ne hh]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
