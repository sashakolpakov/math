import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeSemanticsCode

namespace OAI.Algorithms

/-! Admissibility closure for source expressions whose original literal
identifiers need not equal their free formal-variable type. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open Polynomial _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree NodeSemantics
open scoped BigOperators

variable {V I R : Type*} [DecidableEq V] [CommRing R]

theorem admissible_ringScalar (c : R) : Admissible (Moments.ringScalar (V:=V) c) := by
  rw [Moments.ringScalar_eq_atom]
  exact Sparse.atom_admissible _ _ (by simp [Index.Valid,Index.origin])

theorem admissible_neg {F : Jet V R} (hF : Admissible F) : Admissible (-F) := by
  intro u z
  rw [Polynomial.coeff_neg, Polynomial.coeff_neg]
  intro s hs
  exact hF u z s (by simpa using hs)

theorem admissible_sub {F G : Jet V R} (hF : Admissible F) (hG : Admissible G) :
    Admissible (F-G) := by
  change Admissible (F + -G)
  exact hF.add (admissible_neg hG)

theorem admissible_X : Admissible (Polynomial.X : Jet V R) := by
  simpa only [Polynomial.monomial_one_one_eq_X] using
    admissible_monomial 1 (1 : ZJet V R) zAdmissible_one

theorem admissible_eval₂ (P : R[X]) {F : Jet V R} (hF : Admissible F) :
    Admissible (P.eval₂ Moments.ringScalar F) := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simpa only [Polynomial.eval₂_add] using hp.add hq
  | monomial i c =>
    simpa only [Polynomial.eval₂_monomial] using (admissible_ringScalar c).mul (hF.pow i)

theorem admissible_literal (value : I → Jet V R) (hv : ∀ i, Admissible (value i))
    (l : SAT.Literal I) : Admissible (literalValue (ringAlgebra (Jet V R)) value l) := by
  cases hp : l.positive
  · simpa [literalValue,hp] using hv l.variable
  · simpa [literalValue,hp,ringAlgebra] using
      (admissible_one (V:=V) (R:=R)).add (admissible_neg (hv l.variable))

theorem admissible_clause (value : I → Jet V R) (hv : ∀ i, Admissible (value i))
    (ls : List (SAT.Literal I)) :
    Admissible (clauseValue (ringAlgebra (Jet V R)) value ls) := by
  induction ls with
  | nil => exact admissible_one
  | cons l ls ih => exact (admissible_literal value hv l).mul ih

theorem admissible_row (value : I → Jet V R) (hv : ∀ i, Admissible (value i))
    (ws : SparseRow I R) :
    Admissible (rowValue (ringAlgebra (Jet V R)) (scalarJet (V:=V)) value ws) := by
  induction ws with
  | nil => exact admissible_zero
  | cons w ws ih =>
    have hc : Admissible (scalarJet (V:=V) w.1) := by
      rw [ResidualEmbedding.scalarJet_eq_ringScalar]
      exact admissible_ringScalar w.1
    exact (hc.mul (admissible_clause value hv w.2)).add ih

theorem admissible_indicatorJet (t : ℕ) (digits : Fin t → R[X])
    {F : Jet V R} (hF : Admissible F) : Admissible (indicatorJet t digits F) := by
  apply admissible_sum
  intro s hs
  have h1 : Admissible (1 : Jet V R) := admissible_one
  have h2 : Admissible (2 : Jet V R) := by
    simpa only [one_add_one_eq_two] using h1.add h1
  have hh : Admissible (IdempotentProgram.hValue F) :=
    (hF.mul (admissible_sub hF h1)).mul (admissible_sub hF h2)
  exact ((admissible_X.pow s.val).mul (admissible_eval₂ (digits s) hF)).mul (hh.pow s.val)

theorem admissible_list_prod {A : Type*} (xs : List A) (F : A → Jet V R)
    (hF : ∀ a ∈ xs, Admissible (F a)) : Admissible ((xs.map F).prod) := by
  induction xs with
  | nil => exact admissible_one
  | cons a xs ih =>
    exact (hF a (by simp)).mul (ih (fun b hb => hF b (by simp [hb])))

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
