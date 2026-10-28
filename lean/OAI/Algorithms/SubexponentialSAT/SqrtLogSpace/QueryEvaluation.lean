import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectScores
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramMarked
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsShift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeJet
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRing

/-! Exact natural-valued query semantics. These identities preserve the ambient
assignment type, including coordinates absent from every clause. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation

open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

/-- At zero violation mass, the accepted count is the full CNF count. -/
theorem acceptedCount_eq_count_of_mass_zero {n m : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (rows : List (HashSelect.Row m))
    (hzero : HashSelect.mass (HashSelect.cnfRowAccept clauses)
      (HashInput.violationWeight clauses) rows = 0) :
    HashSelect.acceptedCount (HashSelect.cnfRowAccept clauses) rows =
      SAT.count (Finset.univ.image clauses) := by
  classical
  unfold HashSelect.acceptedCount SAT.count SAT.satisfyingAssignments
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  have h := HashSelect.cnf_mass_zero_iff clauses rows hzero x
  have hcnf : SAT.CNF.eval x (Finset.univ.image clauses) = true ↔
      ∀ i, (clauses i).eval x = true := by
    simp
  simp only [h, hcnf]

/-- Each marked query, just like the unmarked query, counts at most all
assignments over the original declared variables. -/
theorem markedCount_le_two_pow {n m : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (rows : List (HashSelect.Row m))
    (i : Fin m) :
    LeafProgram.markedCount (HashSelect.cnfRowAccept clauses) rows
      (fun e x => !(clauses e).eval x) i ≤ 2 ^ n := by
  simpa [SAT.Assignment] using
    LeafProgram.markedCount_le (HashSelect.cnfRowAccept clauses) rows
      (fun e x => !(clauses e).eval x) i

/-- The greedy score sums actual marked query results and has a fixed binary
width even for candidates that lose the comparison. -/
theorem sum_markedCount_le {n m : ℕ}
    (clauses : Fin m → SAT.Clause (Fin n)) (rows : List (HashSelect.Row m)) :
    (∑ i, LeafProgram.markedCount (HashSelect.cnfRowAccept clauses) rows
      (fun e x => !(clauses e).eval x) i) ≤ m * 2 ^ n := by
  calc
    _ ≤ ∑ _i : Fin m, 2 ^ n :=
      Finset.sum_le_sum fun i _ => markedCount_le_two_pow clauses rows i
    _ = _ := by simp

section SquarefreeBridge

variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- A proof-only multilinear representative of the existing squarefree algebra.
The evaluator never builds this multivariate polynomial or its support list. -/
noncomputable def squarefreePolynomial (f : Squarefree.Poly V R) : MvPolynomial V R :=
  ∑ s ∈ f.coeff.support,
    MvPolynomial.C (f.coeff s) * ∏ v ∈ s.vars, MvPolynomial.X v

theorem eval_squarefreePolynomial (f : Squarefree.Poly V R)
    (x : V → R) (hx : ∀ v, x v * x v = x v) :
    MvPolynomial.eval x (squarefreePolynomial f) = Squarefree.evalHom x hx f := by
  classical
  rw [Squarefree.eval_eq_sum]
  simp [squarefreePolynomial, Finsupp.sum, Squarefree.weight]

omit [DecidableEq V] in
/-- Existing positive-Taylor-degree support control implies the hypothesis of
Boolean finite differences, without a new backend or formal-variable expansion. -/
theorem squarefreePolynomial_totalDegree (f : Squarefree.Poly V R) (q : ℕ)
    (hf : Squarefree.Bounded q f) : (squarefreePolynomial f).totalDegree ≤ q := by
  classical
  nontriviality R using Subsingleton.eq_zero (squarefreePolynomial f)
  unfold squarefreePolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  calc
    (MvPolynomial.C (f.coeff s) * ∏ v ∈ s.vars, MvPolynomial.X v).totalDegree ≤
        0 + ∑ v ∈ s.vars, (MvPolynomial.X v : MvPolynomial V R).totalDegree := by
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add (by simp) (MvPolynomial.totalDegree_finsetProd _ _))
    _ = s.vars.card := by simp
    _ ≤ q := hf s hs

@[simp] theorem evalAt_squarefreePolynomial (U : Finset V) (f : Squarefree.Poly V R) :
    BooleanDifferences.evalAt U (squarefreePolynomial f) =
      Squarefree.evalBool (fun v => decide (v ∈ U)) f := by
  have he : (fun v => if v ∈ U then (1 : R) else 0) =
      Squarefree.boolValue (fun v => decide (v ∈ U)) := by
    funext v
    simp [Squarefree.boolValue]
  rw [BooleanDifferences.evalAt, he]
  exact eval_squarefreePolynomial f _ (Squarefree.boolValue_idempotent _)

/-- Boolean finite differences apply directly to the source's squarefree
coefficients; the original support bound supplies the degree premise. -/
theorem squarefree_sum_eval_differences [Fintype V] {q J : ℕ} (hq : q < J)
    (f : (V → Bool) → Squarefree.Poly V R) (hf : ∀ x, Squarefree.Bounded q (f x)) :
    (∑ x, Squarefree.evalBool x (f x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        (-1 : R) ^ (E.card - U.card) *
          ∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
            Squarefree.evalBool (fun v => decide (v ∈ U)) (f x) := by
  classical
  have htrue (x : V → Bool) :
      (fun v => decide (v ∈ BooleanDifferences.trueSet x)) = x := by
    funext v
    simp [BooleanDifferences.trueSet]
  simpa only [evalAt_squarefreePolynomial, htrue] using
    BooleanDifferences.sum_eval_eq_sum_differences (fun x => squarefreePolynomial (f x))
      (fun x => (squarefreePolynomial_totalDegree (f x) q (hf x)).trans_lt hq)

/-- Substitute correction variables immediately and retain only the two
bounded scalar coefficient indices. -/
noncomputable def specializeDense (t J : ℕ) (x : V → Bool) :
    Squarefree.Jet V R →+* Dense R t J :=
  (Dense.ofPolynomial t J).comp
    (Squarefree.evalJet (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x))

@[simp] theorem coeff_specializeDense (t J : ℕ) (x : V → Bool)
    (f : Squarefree.Jet V R) (u : Fin t) (z : Fin J) :
    ((specializeDense t J x f).coeff u).coeff z =
      Squarefree.evalBool x ((f.coeff u.val).coeff z.val) := by
  simp [specializeDense, Squarefree.coeff_evalJet, Squarefree.evalBool]

/-- All Taylor and lifting coefficients use the same streamed pair family.
The sign is an integer action, so no multiplicativity of readout is needed. -/
theorem dense_jet_finite_differences [Fintype V] (t J : ℕ)
    (f : (V → Bool) → Squarefree.Jet V R)
    (hf : ∀ x, Squarefree.Admissible (f x)) :
    (∑ x, specializeDense t J x (f x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        ((-1 : ℤ) ^ (E.card - U.card)) •
          ∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
            specializeDense t J (fun v => decide (v ∈ U)) (f x) := by
  classical
  ext u z
  simp only [Truncated.coeff_sum, Truncated.coeff_zsmul, coeff_specializeDense]
  simpa only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    squarefree_sum_eval_differences z.isLt
      (fun x => ((f x).coeff u.val).coeff z.val) (fun x => hf x u.val z.val)

section GroupedQuery

open OAI.Algorithms.SubexponentialSAT.SqrtLog.Moments

variable [Fintype V] {G : Type*} [Fintype G] [DecidableEq G]
  {L : G → Type*} [∀ g, DecidableEq (L g)]

/-- The dense computation groups complete factors in the common coefficient
ring. The additive lifting-marker readout occurs only after the group product. -/
theorem grouped_dense_query (t J : ℕ) (head : V → G)
    (label : ∀ g, (Head head g → Bool) → L g)
    (reps : ∀ y : ∀ g, LabelValue label g, ∀ g, LabelBucket label g (y g))
    (A : G → (V → Bool) → Squarefree.Jet V R)
    (hadm : ∀ x, Squarefree.Admissible (∏ g, A g x))
    (hlocal : ∀ (U : Finset V) g x z,
      split head x g = split head z g →
      (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
      specializeDense t J (fun v => decide (v ∈ U)) (A g x) =
        specializeDense t J (fun v => decide (v ∈ U)) (A g z)) :
    Dense.readout (∑ x, specializeDense t J x (∏ g, A g x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        ((-1 : ℤ) ^ (E.card - U.card)) •
          ∑ y : ∀ g, LabelValue label g,
            Dense.readout (∏ g, ∑ a : LabelBucket label g (y g),
              if ∀ v : Head head g, v.val ∈ E → a.val v = true then
                specializeDense t J (fun v => decide (v ∈ U))
                  (A g (assemble head (fun h =>
                    (Function.update (reps y) g a h).val))) else 0) := by
  classical
  rw [dense_jet_finite_differences t J (fun x => ∏ g, A g x) hadm]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro U _
  apply congrArg (fun a => ((-1 : ℤ) ^ (E.card - U.card)) • a)
  have hg := HeadEvaluation.restricted_grouping head label reps E
    (fun g x => specializeDense t J (fun v => decide (v ∈ U)) (A g x))
    (hlocal U)
  have hgroup :
      (∑ x ∈ Finset.univ.filter (fun x : V → Bool => ∀ i ∈ E, x i = true),
        specializeDense t J (fun v => decide (v ∈ U)) (∏ g, A g x)) =
      ∑ y : ∀ g, LabelValue label g, ∏ g,
        ∑ a : LabelBucket label g (y g),
          if ∀ v : Head head g, v.val ∈ E → a.val v = true then
            specializeDense t J (fun v => decide (v ∈ U))
              (A g (assemble head (fun h =>
                (Function.update (reps y) g a h).val))) else 0 := by
    simpa only [Finset.sum_filter, map_prod] using hg
  simpa only [map_sum] using congrArg Dense.readout hgroup

end GroupedQuery

end SquarefreeBridge

section SourceReadout

open Polynomial LeafProgram LeafProgram.NodeSemantics
variable {R : Type*} [CommRing R]

/-- The new bounded array readout is exactly the original shared-marker
coefficient sum, with the same Taylor truncation. -/
theorem dense_readout_source (t J : ℕ) (P : Polynomial (Polynomial R)) :
    Dense.readout (Dense.ofPolynomial t J P) =
      Truncated.ofPolynomial J (Moments.sumUCoeff t P) := by
  ext z
  rw [Dense.coeff_readout, Truncated.coeff_ofPolynomial, Moments.sumUCoeff_coeff]
  simp only [Dense.coeff_ofPolynomial]
  exact Fin.sum_univ_eq_sum_range (fun u => (P.coeff u).coeff z.val) t

/-- Every actual colored factor, including neutral padding and the optional
marked clause, contributes to the one original query polynomial. -/
theorem colored_selected_dense_readout {n : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (t J : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow (Fin n) R)) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (path : ℕ → Fin n → R[X])
    (ids : List ℕ) (hn : ids.Nodup) (hh : ∀ i < hashes.length, i ∈ ids)
    (hm : marked = true → hashes.length ∈ ids) (color : ℕ → G) :
    Dense.readout (∏ g,
      Dense.ofPolynomial t J (((ids.filter (fun i => color i = g)).map
        (selectedExpression t digits hashes marked clause path)).prod)) =
      Truncated.ofPolynomial J (queryPolynomial t digits hashes marked clause path) := by
  rw [← map_prod, prod_colored_lists ids hn color,
    dense_readout_source, selectedExpression_product t digits hashes marked clause path ids hn hh hm,
    queryExpansion_readout]

/-- Shifting at a reconstruction node retains the same source target. -/
theorem colored_selected_dense_shift {n : ℕ} {G : Type*}
    [Fintype G] [DecidableEq G] (t J : ℕ) (digits : Fin t → R[X])
    (hashes : List (SparseRow (Fin n) R)) (marked : Bool)
    (clause : List (SAT.Literal (Fin n))) (path : ℕ → Fin n → R[X]) (theta : R)
    (ids : List ℕ) (hn : ids.Nodup) (hh : ∀ i < hashes.length, i ∈ ids)
    (hm : marked = true → hashes.length ∈ ids) (color : ℕ → G) :
    Dense.readout (∏ g,
      Dense.ofPolynomial t J (((ids.filter (fun i => color i = g)).map
        (selectedExpression t digits hashes marked clause
          (fun j v => shift theta (path j v)))).prod)) =
      Truncated.ofPolynomial J ((queryPolynomial t digits hashes marked clause path).comp
        (Polynomial.X + Polynomial.C theta)) := by
  rw [colored_selected_dense_readout t J digits hashes marked clause _ ids hn hh hm color,
    queryPolynomial_shift, shift_apply]

end SourceReadout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation
