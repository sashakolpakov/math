import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ResidualEmbeddingBranch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramScalarRow
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramLift

namespace OAI.Algorithms

/-! Original literal identifiers may differ from the residual formal-variable
type. High-variable literals are branch constants, and the sparse row circuit
commutes with padding the remaining formal supports into ambient masks. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree LeafProgram
noncomputable section

variable {I V W R : Type*} [DecidableEq V] [DecidableEq W] [CommRing R]

@[simp] theorem jet_scalarJet (e : V ↪ W) (c : R) :
    jet e (scalarJet c) = scalarJet c := by
  rw [scalarJet, jet_atom]
  rfl

theorem scalarJet_eq_ringScalar (c : R) :
    scalarJet (V := V) c = Moments.ringScalar c :=
  (Moments.ringScalar_eq_atom c).symm

/-- Unlike the original convenience theorem, literal identifiers I and formal
squarefree variables V are independent types. -/
theorem scalar_row_source (t J : ℕ) (value : I → Jet V R)
    (terms : SparseRow I R) :
    rowFoldValue (squarefreeAlgebra t J)
      (fun c => canonical t J (scalarJet c))
      (fun v => canonical t J (value v)) terms 0 =
        canonical t J (MvPolynomial.eval value
          (rowPolynomial (R := Jet V R) scalarJet terms)) := by
  have h := rowFoldValue_projected_zero (canonical t J)
    (canonical_mul t J) (scalarJet (V := V)) value terms
  exact h.trans (rowValue_projected_eq_eval (canonical t J)
    (canonical_mul t J) scalarJet value terms)

theorem row_source_jet (e : V ↪ W) (value : I → Jet V R) (terms : SparseRow I R) :
    MvPolynomial.eval (fun i => jet e (value i))
      (rowPolynomial (R := Jet W R) scalarJet terms) =
    jet e (MvPolynomial.eval value (rowPolynomial (R := Jet V R) scalarJet terms)) := by
  have h := map_rowValue (V := I) (C := R) (R := Jet V R) (S := Jet W R)
    (jet e) (scalarJet (V := V) (R := R)) value terms
  simp only [jet_scalarJet, rowValue_eq_eval] at h
  exact h.symm

theorem rowFold_source_jet (e : V ↪ W) (t J : ℕ)
    (value : I → Jet V R) (terms : SparseRow I R) :
    rowFoldValue (squarefreeAlgebra t J)
      (fun c => canonical t J (scalarJet c))
      (fun i => canonical t J (jet e (value i))) terms 0 =
    jet e (canonical t J (MvPolynomial.eval value
      (rowPolynomial (R := Jet V R) scalarJet terms))) := by
  rw [scalar_row_source, row_source_jet, jet_canonical]

section Branch
variable [Fintype V]

def residualValue (H : Finset V) (a : H → Bool) (low : Free H → Jet (Free H) R)
    (v : V) : Jet (Free H) R :=
  if hv : v ∈ H then scalarJet (if a ⟨v, hv⟩ then 1 else 0) else low ⟨v, hv⟩

def ambientValue (H : Finset V) (a : H → Bool) (low : Free H → Jet (Free H) R)
    (v : V) : Jet V R :=
  if hv : v ∈ H then scalarJet (if a ⟨v, hv⟩ then 1 else 0)
  else jet (inclusion H) (low ⟨v, hv⟩)

omit [Fintype V] in
theorem ambientValue_eq (H : Finset V) (a : H → Bool)
    (low : Free H → Jet (Free H) R) (v : V) :
    ambientValue H a low v = jet (inclusion H) (residualValue H a low v) := by
  by_cases hv : v ∈ H <;> simp [ambientValue, residualValue, hv]

omit [Fintype V] in
@[simp] theorem ambientValue_high (H : Finset V) (a : H → Bool)
    (low : Free H → Jet (Free H) R) (v : H) :
    ambientValue H a low v.val = scalarJet (if a v then 1 else 0) := by
  simp [ambientValue, v.property]

omit [Fintype V] in
@[simp] theorem ambientValue_low (H : Finset V) (a : H → Bool)
    (low : Free H → Jet (Free H) R) (v : Free H) :
    ambientValue H a low v.val = jet (inclusion H) (low v) := by
  simp [ambientValue, v.property]

omit [Fintype V] in
/-- A literal on a fixed high coordinate has a scalar value, using the
falsifying-literal convention of the actual clause interpreter. -/
theorem high_literal (H : Finset V) (a : H → Bool)
    (low : Free H → Jet (Free H) R) (l : SAT.Literal V)
    (hl : l.variable ∈ H) :
    literalValue (ringAlgebra (Jet V R)) (ambientValue H a low) l =
      Moments.ringScalar (if l.positive then
        1 - (if a ⟨l.variable, hl⟩ then 1 else 0 : R)
        else (if a ⟨l.variable, hl⟩ then 1 else 0 : R)) := by
  cases hp : l.positive <;>
    simp [literalValue, ringAlgebra, ambientValue, hl, hp,
      scalarJet_eq_ringScalar, sub_eq_add_neg]

omit [Fintype V] in
theorem branch_rowFold_source (H : Finset V) (a : H → Bool)
    (low : Free H → Jet (Free H) R) (t J : ℕ) (terms : SparseRow V R) :
    rowFoldValue (squarefreeAlgebra t J)
      (fun c => canonical t J (scalarJet c))
      (fun v => canonical t J (ambientValue H a low v)) terms 0 =
      jet (inclusion H) (canonical t J (MvPolynomial.eval (residualValue H a low)
        (rowPolynomial (R := Jet (Free H) R) scalarJet terms))) := by
  simp_rw [ambientValue_eq]
  exact rowFold_source_jet (inclusion H) t J (residualValue H a low) terms

omit [Fintype V] in
/-- Every high-touching output support is zero, including after the complete
  weighted-clause fold and canonical U/Z truncation. -/
theorem branch_rowFold_high_zero (H : Finset V) (a : H → Bool)
    (low : Free H → Jet (Free H) R) (t J : ℕ) (terms : SparseRow V R)
    (s : Finset V) (hs : ∃ v ∈ s, v ∈ H) :
    Moments.jetCoeff ⟨s⟩
      (rowFoldValue (squarefreeAlgebra t J)
        (fun c => canonical t J (scalarJet c))
        (fun v => canonical t J (ambientValue H a low v)) terms 0) = 0 := by
  rw [branch_rowFold_source]
  exact high_support_zero H s hs _

end Branch
end
end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
