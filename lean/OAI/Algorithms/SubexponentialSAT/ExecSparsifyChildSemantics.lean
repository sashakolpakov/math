import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyEncoding

namespace OAI.Algorithms

/-! Set semantics of the two actual child-program outputs. -/

namespace SubexponentialSAT.ExecSparsifyChildSemantics

open ExecCNF

theorem core_set {n k : ℕ} {z : ℕ → ℕ}
    (F A : Formula (SAT.Literal (Fin n))) (K : Clause (SAT.Literal (Fin n)))
    (c : Sparsify.Choice (formulaSet F) z k)
    (hcore : c.flower.core = clauseSet K)
    (hselected : SunflowerBranch.clauses c.flower.core c.flower.petals = formulaSet A) :
    formulaSet (ExecCoreChildProgram.result F A K) = c.child false := by
  rw [ExecCoreChildProgram.result_set, ← hcore, ← hselected]
  rfl

theorem petals_set {n k : ℕ} {z : ℕ → ℕ}
    (F A : Formula (SAT.Literal (Fin n))) (K : Clause (SAT.Literal (Fin n)))
    (c : Sparsify.Choice (formulaSet F) z k)
    (hcore : c.flower.core = clauseSet K)
    (hselected : SunflowerBranch.clauses c.flower.core c.flower.petals = formulaSet A) :
    (formulaSet A).image (fun C => C \ clauseSet K) = c.flower.petals := by
  rw [← hcore, ← hselected]
  exact ExecSunflowerCodeTransport.recovered_petals c.flower

theorem petal_set {n k : ℕ} {z : ℕ → ℕ}
    (F A : Formula (SAT.Literal (Fin n))) (K : Clause (SAT.Literal (Fin n)))
    (c : Sparsify.Choice (formulaSet F) z k)
    (hcore : c.flower.core = clauseSet K)
    (hselected : SunflowerBranch.clauses c.flower.core c.flower.petals = formulaSet A) :
    formulaSet (ExecPetalChildProgram.result F A K) = c.child true := by
  have hp := petals_set F A K c hcore hselected
  rw [ExecPetalChildProgram.result_set]
  rw [hp, ← hselected]
  simp only [Sparsify.Choice.child, ite_true, SunflowerBranch.childB, SAT.absorb,
    Finset.union_comm]

theorem children_mass_lt {n k : ℕ} {z : ℕ → ℕ}
    (F A : Formula (SAT.Literal (Fin n))) (K : Clause (SAT.Literal (Fin n)))
    (c : Sparsify.Choice (formulaSet F) z k)
    (hcore : c.flower.core = clauseSet K)
    (hselected : SunflowerBranch.clauses c.flower.core c.flower.petals = formulaSet A) :
    SunflowerBranch.literalMass (formulaSet (ExecCoreChildProgram.result F A K)) <
        SunflowerBranch.literalMass (formulaSet F) ∧
    SunflowerBranch.literalMass (formulaSet (ExecPetalChildProgram.result F A K)) <
        SunflowerBranch.literalMass (formulaSet F) := by
  rw [core_set F A K c hcore hselected, petal_set F A K c hcore hselected]
  exact ⟨c.child_mass_lt false, c.child_mass_lt true⟩

theorem core_codes {n : ℕ} (F A : Formula (SAT.Literal (Fin n)))
    (K : Clause (SAT.Literal (Fin n))) :
    ExecCoreChildProgram.result (ExecSparsifyEncoding.codes F) (ExecSparsifyEncoding.codes A)
        (K.map Encoding.literalCode) =
      ExecSparsifyEncoding.codes (ExecCoreChildProgram.result F A K) :=
  ExecCoreChildProgram.result_map Encoding.literalCode Encoding.literalCode_injective F A K

theorem petal_codes {n : ℕ} (F A : Formula (SAT.Literal (Fin n)))
    (K : Clause (SAT.Literal (Fin n))) :
    ExecPetalChildProgram.result (ExecSparsifyEncoding.codes F) (ExecSparsifyEncoding.codes A)
        (K.map Encoding.literalCode) =
      ExecSparsifyEncoding.codes (ExecPetalChildProgram.result F A K) :=
  ExecPetalChildProgram.result_map Encoding.literalCode Encoding.literalCode_injective F A K

end SubexponentialSAT.ExecSparsifyChildSemantics

end OAI.Algorithms
