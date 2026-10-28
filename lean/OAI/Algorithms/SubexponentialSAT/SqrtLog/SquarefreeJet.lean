import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeBasic
import OAI.Algorithms.SubexponentialSAT.Truncation

namespace OAI.Algorithms

/-! U is the outer polynomial variable, Z the inner one. Support cardinality
is charged only to Z degree; no formal X support is charged to U. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

noncomputable section

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

abbrev ZJet (V R : Type*) [DecidableEq V] [Semiring R] := Polynomial (Poly V R)
abbrev Jet (V R : Type*) [DecidableEq V] [Semiring R] := Polynomial (ZJet V R)

def ZAdmissible (f : ZJet V R) : Prop := ∀ j, Bounded j (f.coeff j)
def Admissible (f : Jet V R) : Prop := ∀ u, ZAdmissible (f.coeff u)

theorem zAdmissible_zero : ZAdmissible (0 : ZJet V R) := by
  intro j; simpa using bounded_zero (V := V) (R := R) j

theorem zAdmissible_one : ZAdmissible (1 : ZJet V R) := by
  intro j
  by_cases hj : j = 0
  · subst j; simpa using bounded_one (V := V) (R := R)
  · simpa [Polynomial.coeff_one, hj] using bounded_zero (V := V) (R := R) j

theorem ZAdmissible.add {f g : ZJet V R} (hf : ZAdmissible f) (hg : ZAdmissible g) :
    ZAdmissible (f + g) := by
  intro j
  simpa using (hf j).add (hg j)

theorem zAdmissible_sum {ι : Type*} (s : Finset ι) (f : ι → ZJet V R)
    (h : ∀ i ∈ s, ZAdmissible (f i)) : ZAdmissible (∑ i ∈ s, f i) := by
  intro j
  simp only [Polynomial.finsetSum_coeff]
  exact bounded_sum s (fun i => (f i).coeff j) j (fun i hi => h i hi j)

theorem ZAdmissible.mul {f g : ZJet V R} (hf : ZAdmissible f) (hg : ZAdmissible g) :
    ZAdmissible (f * g) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply bounded_sum
  intro ab hab
  have hsum : ab.1 + ab.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  simpa [hsum] using (hf ab.1).mul (hg ab.2)

theorem zAdmissible_monomial (j : ℕ) (f : Poly V R) (hf : Bounded j f) :
    ZAdmissible (Polynomial.monomial j f) := by
  intro l
  by_cases h : j = l
  · subst l; simpa using hf
  · simpa [Polynomial.coeff_monomial, h] using bounded_zero (V := V) (R := R) l

theorem zAdmissible_variable (j : ℕ) (v : V) (c : R) (hj : 1 ≤ j) :
    ZAdmissible (Polynomial.monomial j (monomial {v} c)) :=
  zAdmissible_monomial j _ (bounded_monomial {v} c (by simpa using hj))

theorem ZAdmissible.trunc {f : ZJet V R} (hf : ZAdmissible f) (J : ℕ) :
    ZAdmissible (Truncation.trunc J f) := by
  intro j
  by_cases h : j < J
  · simpa [h] using hf j
  · simpa [h] using bounded_zero (V := V) (R := R) j

theorem admissible_zero : Admissible (0 : Jet V R) := by
  intro u; simpa using zAdmissible_zero (V := V) (R := R)

theorem admissible_one : Admissible (1 : Jet V R) := by
  intro u
  by_cases h : u = 0
  · subst u; simpa using zAdmissible_one (V := V) (R := R)
  · simpa [Polynomial.coeff_one, h] using zAdmissible_zero (V := V) (R := R)

theorem Admissible.add {f g : Jet V R} (hf : Admissible f) (hg : Admissible g) :
    Admissible (f + g) := by
  intro u; simpa using (hf u).add (hg u)

theorem admissible_sum {ι : Type*} (s : Finset ι) (f : ι → Jet V R)
    (h : ∀ i ∈ s, Admissible (f i)) : Admissible (∑ i ∈ s, f i) := by
  intro u
  simp only [Polynomial.finsetSum_coeff]
  exact zAdmissible_sum s (fun i => (f i).coeff u) (fun i hi => h i hi u)

theorem Admissible.mul {f g : Jet V R} (hf : Admissible f) (hg : Admissible g) :
    Admissible (f * g) := by
  intro u
  rw [Polynomial.coeff_mul]
  apply zAdmissible_sum
  intro ab _
  exact (hf ab.1).mul (hg ab.2)

theorem admissible_monomial (u : ℕ) (f : ZJet V R) (hf : ZAdmissible f) :
    Admissible (Polynomial.monomial u f) := by
  intro l
  by_cases h : u = l
  · subst l; simpa using hf
  · simpa [Polynomial.coeff_monomial, h] using zAdmissible_zero (V := V) (R := R)

theorem Admissible.pow {f : Jet V R} (hf : Admissible f) (n : ℕ) :
    Admissible (f ^ n) := by
  induction n with
  | zero => simpa using admissible_one (V := V) (R := R)
  | succ n ih => simpa [pow_succ] using ih.mul hf

theorem admissible_prod {ι : Type*} (s : Finset ι) (f : ι → Jet V R)
    (h : ∀ i ∈ s, Admissible (f i)) : Admissible (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using admissible_one (V := V) (R := R)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (h i (Finset.mem_insert_self _ _)).mul
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Canonical finite U and Z truncation. No enumeration of X supports occurs. -/
def canonical (t J : ℕ) : Jet V R →+ Jet V R :=
  Truncation.clipAddHom t (Truncation.truncAddHom J)

@[simp] theorem coeff_canonical (t J u j : ℕ) (f : Jet V R) :
    ((canonical t J f).coeff u).coeff j =
      if u < t ∧ j < J then (f.coeff u).coeff j else 0 := by
  by_cases hu : u < t <;> by_cases hj : j < J <;>
    simp [canonical, Truncation.coeff_clipAddHom, Truncation.truncAddHom, hu, hj]

theorem Admissible.canonical {f : Jet V R} (hf : Admissible f) (t J : ℕ) :
    Admissible (canonical t J f) := by
  intro u j
  by_cases h : u < t ∧ j < J
  · simpa [h] using hf u j
  · simpa [h] using bounded_zero (V := V) (R := R) j

theorem canonical_mul (t J : ℕ) (f g : Jet V R) :
    canonical t J (canonical t J f * canonical t J g) = canonical t J (f * g) := by
  apply Truncation.clipAddHom_mul
  intro a b
  have h := Truncation.clipAddHom_mul J (AddMonoidHom.id (Poly V R))
    (fun _ _ => rfl) a b
  simpa [Truncation.clipAddHom, Truncation.truncAddHom,
    Truncation.mapCoeffs, AddMonoidHom.comp_apply] using h

theorem retained_support_lt {f : Jet V R} (hf : Admissible f)
    (t J u j : ℕ) (s : Finset V)
    (h : coeff s (((canonical t J f).coeff u).coeff j) ≠ 0) : s.card < J := by
  by_cases huv : u < t ∧ j < J
  · have hmem : Support.mk s ∈
        (MonoidAlgebra.coeff ((f.coeff u).coeff j)).support := by
      apply Finsupp.mem_support_iff.mpr
      simpa [coeff, huv] using h
    exact (hf u j _ hmem).trans_lt huv.2
  · simp [huv] at h

def evalJet (x : V → R) (hx : ∀ v, x v * x v = x v) :
    Jet V R →+* Polynomial (Polynomial R) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (evalHom x hx))

@[simp] theorem coeff_evalJet (x : V → R) (hx : ∀ v, x v * x v = x v)
    (f : Jet V R) (u j : ℕ) :
    (((evalJet x hx) f).coeff u).coeff j = evalHom x hx ((f.coeff u).coeff j) := by
  simp [evalJet]

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
