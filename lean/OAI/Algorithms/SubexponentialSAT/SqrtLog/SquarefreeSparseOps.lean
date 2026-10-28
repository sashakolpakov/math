import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparseProduct

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

namespace Index

variable {V : Type*} [DecidableEq V]

def origin : Index V := ⟨0, 0, ∅⟩

@[simp] theorem origin_join (a : Index V) : origin.join a = a := by
  cases a; simp [origin, join]

end Index

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

def zero : Data (Index V) R := []

def constant (t J : ℕ) (c : R) : Data (Index V) R :=
  if 0 < t ∧ 0 < J then [(Index.origin, c)] else []

def one (t J : ℕ) : Data (Index V) R := constant t J 1

def scale (c : R) (l : Data (Index V) R) : Data (Index V) R :=
  l.map (fun a => (a.1, c * a.2))

def clip (t J : ℕ) (l : Data (Index V) R) : Data (Index V) R :=
  normalize (l.filter (fun a => decide (a.1.Kept t J)))

@[simp] theorem denote_zero : denote (zero : Data (Index V) R) = 0 := rfl

theorem denote_add (a b : Data (Index V) R) : denote (add a b) = denote a + denote b :=
  decode_add atom atom_zero atom_add a b

theorem denote_constant (t J : ℕ) (c : R) :
    denote (constant (V := V) t J c) = canonical t J (atom Index.origin c) := by
  rw [canonical_atom]
  by_cases h : 0 < t ∧ 0 < J <;> simp [constant, Index.Kept, Index.origin, h, denote, decode]

@[simp] theorem atom_origin_one : atom (Index.origin : Index V) (1 : R) = 1 := by
  change Polynomial.monomial 0 (Polynomial.monomial 0 (1 : Poly V R)) = 1
  simp

theorem denote_one (t J : ℕ) :
    denote (one (V := V) (R := R) t J) = canonical t J 1 := by
  rw [one, denote_constant, atom_origin_one]

theorem denote_scale (c : R) (l : Data (Index V) R) :
    denote (scale c l) = atom Index.origin c * denote l := by
  induction l with
  | nil => simp [scale, denote, decode]
  | cons a l ih =>
      simp only [scale, List.map_cons, denote, decode, mul_add]
      rw [atom_mul, Index.origin_join]
      exact congrArg (atom a.1 (c * a.2) + ·) ih

theorem denote_filter (t J : ℕ) (l : Data (Index V) R) :
    denote (l.filter (fun a => decide (a.1.Kept t J))) = canonical t J (denote l) := by
  induction l with
  | nil => simp [denote, decode]
  | cons a l ih =>
      by_cases h : a.1.Kept t J <;>
        simp [ h, denote, decode, map_add, canonical_atom, ih]

theorem denote_clip (t J : ℕ) (l : Data (Index V) R) :
    denote (clip t J l) = canonical t J (denote l) := by
  rw [clip, denote, decode_normalize atom atom_zero atom_add]
  exact denote_filter t J l

omit [DecidableEq V] in
@[simp] theorem scale_length (c : R) (l : Data (Index V) R) : (scale c l).length = l.length :=
  List.length_map _

omit [DecidableEq V] in
@[simp] theorem keys_scale (c : R) (l : Data (Index V) R) : keys (scale c l) = keys l := by
  simp [keys, scale, List.map_map, Function.comp_def]

noncomputable def jetCoeff (a : Index V) (f : Jet V R) : R :=
  coeff a.vars ((f.coeff a.u).coeff a.z)

theorem jetCoeff_atom (a b : Index V) (c : R) :
    jetCoeff a (atom b c) = if b = a then c else 0 := by
  rcases a with ⟨u, z, s⟩
  rcases b with ⟨v, w, t⟩
  by_cases hu : v = u <;> by_cases hz : w = z <;> by_cases hs : t = s <;>
    simp [jetCoeff, atom, Polynomial.coeff_monomial, coeff_monomial, hu, hz, hs]

theorem jetCoeff_denote (a : Index V) (l : Data (Index V) R) :
    jetCoeff a (denote l) = fetch a l := by
  induction l with
  | nil => simp [denote, decode, jetCoeff, fetch]
  | cons b l ih =>
      change jetCoeff a (atom b.1 b.2 + denote l) = _
      simp only [jetCoeff, Polynomial.coeff_add, coeff_add]
      change jetCoeff a (atom b.1 b.2) + jetCoeff a (denote l) = _
      rw [jetCoeff_atom, ih]
      rfl

end Sparse

namespace Sparse

variable {V R : Type*} [DecidableEq V] [CommRing R]

def neg (l : Data (Index V) R) : Data (Index V) R := l.map (fun a => (a.1, -a.2))

theorem denote_neg (l : Data (Index V) R) : denote (neg l) = -denote l := by
  induction l with
  | nil =>
      ext u z s
      simp [neg, denote, decode, Polynomial.coeff_neg]
  | cons a l ih =>
      have ha : atom a.1 (-a.2) = -atom a.1 a.2 := by
        simp [atom, monomial]
      simp only [neg, List.map_cons, denote, decode]
      rw [ha]
      change -atom a.1 a.2 + denote (neg l) = -(atom a.1 a.2 + denote l)
      rw [ih]
      ext u z s
      simp [Polynomial.coeff_neg, Polynomial.coeff_add, add_comm]

end Sparse
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
