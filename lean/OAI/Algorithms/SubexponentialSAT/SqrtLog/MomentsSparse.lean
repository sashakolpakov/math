import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsSquarefree
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsCanonical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparseBounds

namespace OAI.Algorithms

/-! Executable support extraction for the normalized sparse squarefree jets.
Projection erases X after extracting one requested support, leaving U and Z.
All operations preserve the same bounded sparse representation. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

noncomputable def projectSupport (s : Finset V) (f : Jet V R) : Jet V R :=
  jetScalar (jetCoeff ⟨s⟩ f)

noncomputable def ringScalar : R →+* Jet V R :=
  Polynomial.C.comp (Polynomial.C.comp Squarefree.scalar)

@[simp] theorem scalar_empty (c : R) :
    (Squarefree.scalar c : Poly V R) = Squarefree.monomial ∅ c := rfl

theorem ringScalar_eq_atom (c : R) :
    ringScalar (V := V) c = Sparse.atom Index.origin c := by
  simp [ringScalar, Sparse.atom, Index.origin]

@[simp] theorem monomial_zero (s : Finset V) : (Squarefree.monomial s (0 : R)) = 0 := by
  simp [Squarefree.monomial]

theorem projectSupport_add (s : Finset V) (f g : Jet V R) :
    projectSupport s (f + g) = projectSupport s f + projectSupport s g := by
  simp [projectSupport]

@[simp] theorem projectSupport_zero (s : Finset V) :
    projectSupport s (0 : Jet V R) = 0 := by simp [projectSupport]

theorem projectSupport_atom (s : Finset V) (a : Index V) (c : R) :
    projectSupport s (Sparse.atom a c) =
      if a.vars = s then Sparse.atom ⟨a.u, a.z, ∅⟩ c else 0 := by
  classical
  ext u z v
  by_cases hu : a.u = u <;> by_cases hz : a.z = z <;> by_cases hs : a.vars = s <;>
    simp [projectSupport, jetScalar, Sparse.atom, jetCoeff_apply,
      Polynomial.coeff_monomial, coeff_monomial, hu, hz, hs, scalar_empty ]

theorem projectSupport_canonical (s : Finset V) (t J : ℕ) (f : Jet V R) :
    projectSupport s (canonical t J f) = canonical t J (projectSupport s f) := by
  ext u z
  by_cases h : u < t ∧ z < J <;>
    simp [projectSupport, jetScalar, coeff_canonical, h]

def rawProject (s : Finset V) : Sparse.Data (Index V) R → Sparse.Data (Index V) R
  | [] => []
  | a :: l => if a.1.vars = s then (⟨a.1.u, a.1.z, ∅⟩, a.2) :: rawProject s l
      else rawProject s l

def sparseProject (s : Finset V) (l : Sparse.Data (Index V) R) :=
  Sparse.normalize (rawProject s l)

theorem denote_rawProject (s : Finset V) (l : Sparse.Data (Index V) R) :
    Sparse.denote (rawProject s l) = projectSupport s (Sparse.denote l) := by
  induction l with
  | nil => simp [rawProject, Sparse.denote, Sparse.decode]
  | cons a l ih =>
      change Sparse.denote (if a.1.vars = s then _ else _) =
        projectSupport s (Sparse.atom a.1 a.2 + Sparse.denote l)
      rw [projectSupport_add, projectSupport_atom]
      by_cases h : a.1.vars = s
      · simpa [h, Sparse.denote, Sparse.decode] using
          congrArg (Sparse.atom ⟨a.1.u, a.1.z, ∅⟩ a.2 + ·) ih
      · simpa [h] using ih

theorem denote_sparseProject (s : Finset V) (l : Sparse.Data (Index V) R) :
    Sparse.denote (sparseProject s l) = projectSupport s (Sparse.denote l) := by
  rw [sparseProject, Sparse.denote,
    Sparse.decode_normalize Sparse.atom Sparse.atom_zero Sparse.atom_add]
  exact denote_rawProject s l

omit [CommSemiring R] in
theorem rawProject_valid {vars : Finset V} {t J : ℕ}
    (s : Finset V) (l : Sparse.Data (Index V) R) (hl : Sparse.ValidData vars t J l) :
    Sparse.ValidData vars t J (rawProject s l) := by
  induction l with
  | nil => simp [rawProject, Sparse.ValidData, Sparse.keys]
  | cons a l ih =>
      have ha := hl a.1 (by simp [Sparse.keys])
      have ht : Sparse.ValidData vars t J l := by
        intro q hq
        apply hl q
        simpa [Sparse.keys] using Or.inr hq
      have hi := ih ht
      by_cases h : a.1.vars = s
      · intro q hq
        simp only [rawProject, h, ite_true, Sparse.keys, List.map_cons, List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact ⟨ha.1, Nat.zero_le _, Finset.empty_subset _⟩
        · exact hi q hq
      · simpa [rawProject, h] using hi

omit [CommSemiring R] in
theorem rawProject_length_le (s : Finset V) (l : Sparse.Data (Index V) R) :
    (rawProject s l).length ≤ l.length := by
  induction l with
  | nil => simp [rawProject]
  | cons a l ih =>
      by_cases h : a.1.vars = s <;> simp [rawProject, h] <;> omega

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
