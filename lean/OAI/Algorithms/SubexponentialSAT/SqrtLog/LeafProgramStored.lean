import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSquarefree
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsStored
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparseRing

namespace OAI.Algorithms

/-! The sparse hash evaluator instantiated with actual normalized coefficient
lists. These are executable finite list operations. Counters are dictionary
and ring-operation counts; the bit-program implementation must refine them. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.SubexpSymbolicCost
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {V R : Type*} [DecidableEq V] [CommRing R]
variable {vars : Finset V} {t J : ℕ}

def storedNeg (a : Moments.Stored (R := R) vars t J) : Moments.Stored (R := R) vars t J :=
  ⟨Sparse.neg a.data, a.valid.neg, Sparse.neg_nodup a.nodup⟩

def storedOps : RingProgram (Moments.Stored (R := R) vars t J) where
  zeroRun := (Moments.Stored.zero, 1)
  oneRun := (Moments.Stored.one, 1)
  addRun a b := (Moments.Stored.add a b, Sparse.normalizeWork (a.data ++ b.data))
  mulRun a b := (Moments.Stored.mul a b, Sparse.mulWork t J a.data b.data)
  negRun a := (storedNeg a, a.data.length)

theorem storedOps_represents :
    Represents (storedOps (R := R) (vars := vars) (t := t) (J := J))
      (squarefreeAlgebra t J) Moments.Stored.denote where
  zero := rfl
  one := Sparse.denote_one t J
  add a b := Sparse.denote_add a.data b.data
  mul a b := Sparse.denote_mul t J a.data b.data
  neg a := Sparse.denote_neg a.data

/-- One uniform structural bound for any normalized sparse operation. -/
def storedBudget (vars : Finset V) (t J : ℕ) : ℕ :=
  let L := Moments.Stored.sizeBound vars t J
  1 + 2 * L * (2 * L + 1) + L ^ 2 * (2 * L + 2) + L

theorem storedOps_budget :
    ProgramBudget (storedOps (R := R) (vars := vars) (t := t) (J := J))
      (storedBudget vars t J) where
  zero := by simp [storedOps, storedBudget]; omega
  one := by simp [storedOps, storedBudget]; omega
  add a b := by
    have h := Moments.Stored.add_cost a b
    change Sparse.normalizeWork (a.data ++ b.data) ≤ _
    change Sparse.normalizeWork (a.data ++ b.data) ≤ _ at h
    dsimp [storedBudget]
    omega
  mul a b := by
    have h := Moments.Stored.mul_cost a b
    change Sparse.mulWork t J a.data b.data ≤ _
    change Sparse.mulWork t J a.data b.data ≤ _ at h
    dsimp [storedBudget]
    omega
  neg a := by
    have h := a.length_le
    change a.data.length ≤ _
    dsimp [storedBudget, Moments.Stored.sizeBound]
    omega

/-- Actual normalized hash evaluation denotes the canonical truncation of the
single source polynomial. The validity proof in `Stored` also bounds every
intermediate dictionary, including literal complements and clause products. -/
theorem stored_rowRun_eq_eval
    (value : V → Moments.Stored (R := R) vars t J × ℕ)
    (terms : SparseRow V (Moments.Stored (R := R) vars t J)) :
    Moments.Stored.denote (rowRun storedOps value terms).1 =
      Squarefree.canonical t J
        (MvPolynomial.eval (fun v => (value v).1.denote)
          (rowPolynomial (R := Squarefree.Jet V R)
            (fun a : Moments.Stored (R := R) vars t J => a.denote) terms)) := by
  rw [rowRun_correct storedOps (squarefreeAlgebra t J) Moments.Stored.denote
    storedOps_represents]
  have h := squarefree_rowValue t J
    (fun a : Moments.Stored (R := R) vars t J => a.denote)
    (fun v => (value v).1.denote) terms
  simpa only [Moments.Stored.canonical] using h

theorem stored_rowRun_cost {b k : ℕ}
    (value : V → Moments.Stored (R := R) vars t J × ℕ)
    (hv : ∀ v, (value v).2 ≤ b)
    (terms : SparseRow V (Moments.Stored (R := R) vars t J))
    (hk : ∀ term ∈ terms, term.2.length ≤ k) :
    (rowRun storedOps value terms).2 ≤ storedBudget vars t J + terms.length *
      (3 * storedBudget vars t J + k * (b + 4 * storedBudget vars t J + 2) + 1) :=
  rowRun_cost storedOps storedOps_budget value hv terms hk

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
