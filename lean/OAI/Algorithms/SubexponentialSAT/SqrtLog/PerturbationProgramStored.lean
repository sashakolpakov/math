import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpDensePolynomial
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree Squarefree.Sparse

variable {C R V : Type*} [CommRing R] [DecidableEq V]

/-- Coefficient emission scans the explicit list once. No monomial universe is
constructed; j is a unary exponent field of polynomially bounded value. -/
def coefficientRecords (v : V) : ℕ → List C → List (Index V × C)
  | _, [] => []
  | j, c :: cs => (⟨0,j,{v}⟩,c) :: coefficientRecords v (j+1) cs

omit [DecidableEq V] in
@[simp] theorem coefficientRecords_length (v : V) (j : ℕ) (p : List C) :
    (coefficientRecords v j p).length = p.length := by
  induction p generalizing j with
  | nil => rfl
  | cons c cs ih => simp [coefficientRecords, ih]

def decodeRecords (ops : RepresentedRing C R) (l : List (Index V × C)) :
    Sparse.Data (Index V) R := l.map (fun a => (a.1,ops.decode a.2))

private theorem variableZ_add (v : V) (p q : Polynomial R) :
    Moments.variableZ v (p+q) = Moments.variableZ v p + Moments.variableZ v q := by
  simp [Moments.variableZ, add_mul]

private theorem atom_variable (v : V) (j : ℕ) (c : R) :
    atom (⟨0,j,{v}⟩ : Index V) c =
      Polynomial.C (Moments.variableZ v (Polynomial.monomial j c)) := by
  change Polynomial.C (Polynomial.monomial j (monomial {v} c)) = _
  congr 1
  ext z
  rw [Moments.variableZ_coeff]
  by_cases h : j = z <;> simp [Polynomial.coeff_monomial, h]

/-- Exact meaning of the emitted coefficient stream, before precision clipping. -/
theorem coefficientRecords_denote (ops : RepresentedRing C R) (v : V)
    (j : ℕ) (p : List C) :
    Sparse.denote (decodeRecords ops (coefficientRecords v j p)) =
      Polynomial.C (Moments.variableZ v (Polynomial.X^j * polynomial ops p)) := by
  induction p generalizing j with
  | nil => simp [coefficientRecords, decodeRecords, Sparse.denote, Sparse.decode,
      polynomial, SubexpDensePolynomial.decodeList, Moments.variableZ]
  | cons c cs ih =>
      change atom (⟨0,j,{v}⟩ : Index V) (ops.decode c) +
        Sparse.denote (decodeRecords ops (coefficientRecords v (j+1) cs)) = _
      rw [atom_variable, ih, ← Polynomial.C_add, ← variableZ_add]
      congr 2
      simp only [polynomial, SubexpDensePolynomial.decodeList, List.map_cons,
        PolynomialAlgorithm.denote_cons]
      rw [mul_add, pow_succ]
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      ring

omit [DecidableEq V] in
private theorem coefficientRecords_mem (v : V) (j : ℕ) (p : List C)
    (a : Index V × C) (ha : a ∈ coefficientRecords v j p) :
    a.1.u = 0 ∧ j ≤ a.1.z ∧ a.1.vars = {v} := by
  induction p generalizing j with
  | nil => simp [coefficientRecords] at ha
  | cons c cs ih =>
      rcases List.mem_cons.mp ha with h | h
      · subst a; exact ⟨rfl,le_rfl,rfl⟩
      · obtain ⟨hu,hj,hv⟩ := ih (j+1) h
        exact ⟨hu,by omega,hv⟩

/-- The origin is constructed by the same clipped constant record operation
used by Stored.one; beta is an actual computed coefficient. -/
def constantStored (vars : Finset V) (t J : ℕ) (beta : R) :
    Moments.Stored (R := R) vars t J :=
  ⟨Sparse.constant t J beta, Sparse.constant_valid vars t J beta,
    by by_cases h : 0 < t ∧ 0 < J <;> simp [Sparse.constant,h,Sparse.keys]⟩

/-- Positive powers make each singleton record admissible, including before
clipping. Normalization is the explicit finite Sparse.normalize operation. -/
def positiveStored (ops : RepresentedRing C R) (vars : Finset V) (v : V)
    (hv : v ∈ vars) (t J : ℕ) (p : List C) : Moments.Stored (R := R) vars t J where
  data := Sparse.clip t J (decodeRecords ops (coefficientRecords v 1 p))
  valid := by
    apply Sparse.ValidData.normalize
    intro a ha
    obtain ⟨b,hb,hab⟩ := List.mem_map.mp ha
    obtain ⟨hb,hkeep⟩ := List.mem_filter.mp hb
    obtain ⟨c,hc,hcb⟩ := List.mem_map.mp hb
    subst b
    subst a
    obtain ⟨hu,hz,hs⟩ := coefficientRecords_mem v 1 p c hc
    refine ⟨of_decide_eq_true hkeep, ?_, ?_⟩
    · simp only [Index.Valid, hs, Finset.card_singleton]
      exact hz
    · simpa [hs] using (Finset.singleton_subset_iff.mpr hv)
  nodup := Sparse.nodup_normalize _

@[simp] theorem constantStored_denote (vars : Finset V) (t J : ℕ) (beta : R) :
    (constantStored vars t J beta).denote = canonical t J (atom Index.origin beta) :=
  Sparse.denote_constant t J beta

theorem positiveStored_denote (ops : RepresentedRing C R) (vars : Finset V) (v : V)
    (hv : v ∈ vars) (t J : ℕ) (p : List C) :
    (positiveStored ops vars v hv t J p).denote =
      canonical t J (Polynomial.C (Moments.variableZ v (Polynomial.X * polynomial ops p))) := by
  change Sparse.denote (Sparse.clip t J _) = _
  rw [Sparse.denote_clip, coefficientRecords_denote]
  simp

/-- The translated tail is materialized from the input coefficients. -/
def coordinateStored (ops : RepresentedRing C R) (vars : Finset V) (v : V)
    (hv : v ∈ vars) (t J : ℕ) (theta : C) (p : List C) :
    Moments.Stored (R := R) vars t J :=
  positiveStored ops vars v hv t J (coordinateRun ops theta p).1.2.tail

theorem coordinateStored_denote (ops : RepresentedRing C R) (vars : Finset V) (v : V)
    (hv : v ∈ vars) (t J : ℕ) (theta : C) (p : List C) :
    (coordinateStored ops vars v hv t J theta p).denote =
      canonical t J (Polynomial.C (Moments.variableZ v
        (Moments.rowDelta (polynomial ops p) (ops.decode theta)))) := by
  rw [coordinateStored, positiveStored_denote]
  have h : Polynomial.X * polynomial ops (coordinateRun ops theta p).1.2.tail =
      polynomial ops (positiveRun ops theta p) := by
    simp [polynomial, positiveRun, SubexpDensePolynomial.decodeList, ops.zero_correct]
  rw [h, positiveRun_correct]

end SubexponentialSAT.SqrtLog.PerturbationProgram

end OAI.Algorithms
