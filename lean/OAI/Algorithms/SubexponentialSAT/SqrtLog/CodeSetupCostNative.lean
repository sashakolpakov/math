import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCostPolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupCost
open CostAssembly Asymptotic Filter
open scoped Topology

theorem localProgramBudget_eq (t D d : ℕ) :
    CodeSearchProgram.localProgramBudget t D d =
      localNumeric (CodeSearchProgram.alphabetBits 3).length
        (SubexponentialSAT.SubexpEnumerationPayload.scalarWidth 3) t D d (t*D) (3^D) (3^(t*D)) := by
  unfold CodeSearchProgram.localProgramBudget CodeSearchProgram.generateBudget
    CodeSearchProgram.framedEnumerationCost CodeSearchProgram.matrixSearchBudget
    CodeSearchProgram.candidateBudget CodeSearchProgram.localVerifierBudget
    CodeSearchProgram.callbackBudget CodeSearchProgram.wordBudget
    CodeSearchProgram.wordInputSpan CodeSearchProgram.wordTailBudget
    CodeSearchProgram.wordRecordsLength SubexponentialSAT.Subexp.MatrixVectorProgram.matrixBudget
    SubexponentialSAT.Subexp.MatrixVectorProgram.rowBudget SubexponentialSAT.Subexp.MatrixProgram.termBudget
    localNumeric generation localCandidate localVerifier localCallback localWord matrix2
  ring

theorem graphProgramBudget_eq (D r qlen Dlen : ℕ) :
    CodeSearchProgram.graphProgramBudget D r qlen Dlen =
      graphNumeric (CodeSearchProgram.alphabetBits 2).length
        (SubexponentialSAT.SubexpEnumerationPayload.scalarWidth 2) D r qlen Dlen (D*r) (2^r) (2^(D*r)) := by
  unfold CodeSearchProgram.graphProgramBudget CodeSearchProgram.generateBudget
    CodeSearchProgram.framedEnumerationCost CodeSearchProgram.graphSearchBudget
    CodeSearchProgram.graphCandidateBudget CodeSearchProgram.graphVerifierBudget
    CodeSearchProgram.graphCallbackBudget CodeSearchProgram.graphWordBudget
    CodeSearchProgram.graphCountsBudget CodeSearchProgram.graphInputSpan
    CodeSearchProgram.characterRecordsLength SubexponentialSAT.Subexp.MatrixVectorProgram.matrixBudget
    SubexponentialSAT.Subexp.MatrixVectorProgram.rowBudget SubexponentialSAT.Subexp.MatrixProgram.termBudget
    graphNumeric generation graphCandidate graphVerifier graphCallback graphWord matrix2
  ring

def fixedConstant (f g : ℕ) : ℕ :=
  1000000000000*(f+g+1)+(CodeSearchProgram.alphabetBits 2).length+
    (CodeSearchProgram.alphabetBits 3).length+
    SubexponentialSAT.SubexpEnumerationPayload.scalarWidth 2+SubexponentialSAT.SubexpEnumerationPayload.scalarWidth 3

def nativeBudget (f g t D d r qlen Dlen : ℕ) : ℕ :=
  f*CodeSearchProgram.localProgramBudget t D d+
    g*CodeSearchProgram.graphProgramBudget D r qlen Dlen+1

theorem nativeBudget_le (f g t D d r qlen Dlen H W : ℕ)
    (ht : t ≤ H) (hD : D ≤ H) (hd : d ≤ H) (hr : r ≤ H)
    (hq : qlen ≤ W) (hDl : Dlen ≤ W) :
    nativeBudget f g t D d r qlen Dlen ≤ envelope (fixedConstant f g) H W := by
  simpa only [nativeBudget,localProgramBudget_eq,graphProgramBudget_eq] using
    combinedNumeric_bound (CodeSearchProgram.alphabetBits 2).length
      (CodeSearchProgram.alphabetBits 3).length (SubexponentialSAT.SubexpEnumerationPayload.scalarWidth 2)
      (SubexponentialSAT.SubexpEnumerationPayload.scalarWidth 3) t D d r qlen Dlen f g H W
      (fixedConstant f g) ht hD hd hr hq hDl (by rfl)

def height (m B : ℕ) : ℕ := SparseCode.degree m B+SparseCode.logSize m+2

def heightCoefficient (q : ℕ) : ℕ := 320000*(q+2)^3+q+4

theorem height_le (n m B q : ℕ) (hm : m ≤ n*B) (hB : B ≤ L n^q) :
    height m B ≤ heightCoefficient q * L n^(2*q+3) := by
  have hd := (SparseCode.degree_le_bound m B).trans (code_degreeBound_le n m B q hm hB)
  have hl := code_logSize_le n m B q hm hB
  have hpow : L n ≤ L n^(2*q+3) := by
    simpa using Nat.pow_le_pow_right (L_pos n) (by omega : 1 ≤ 2*q+3)
  have hpos : 1 ≤ L n^(2*q+3) := Nat.one_le_pow _ _ (L_pos n)
  unfold height heightCoefficient
  nlinarith

def constructedBudget (f g m B qlen Dlen : ℕ) : ℕ :=
  nativeBudget f g (SparseCode.localRows m B) (SparseCode.degree m B)
    (SparseCode.degree m B/(100*B*SparseCode.logSize m)+1)
    (SparseCode.dimension m B) qlen Dlen

theorem constructedBudget_le (f g m B qlen Dlen : ℕ)
    (hm : 0 < m) (hB : 0 < B) :
    constructedBudget f g m B qlen Dlen ≤
      envelope (fixedConstant f g) (height m B) (max qlen Dlen) := by
  apply nativeBudget_le
  · have hdiv := Nat.div_le_self (SparseCode.degree m B) (8*B)
    unfold SparseCode.localRows height
    omega
  · unfold height; omega
  · have hdiv := Nat.div_le_self (SparseCode.degree m B) (100*B*SparseCode.logSize m)
    unfold height
    omega
  · have hh := SparseCode.dimension_lt_logSize hm hB
    unfold height
    omega
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- Uniform in every admissible leaf, both fixed search-machine multipliers,
and all metadata encodings whose physical lengths satisfy the shown bound. -/
theorem eventually_constructedBudget (f g q u : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀m B qlen Dlen:ℕ,
      0 < m → 0 < B → m ≤ n*B → B ≤ L n^q →
      qlen ≤ (n+1)^u → Dlen ≤ (n+1)^u →
      (constructedBudget f g m B qlen Dlen:ℝ) ≤ (2:ℝ)^Statement.runtimeScale n := by
  filter_upwards [eventually_envelope (fixedConstant f g) (heightCoefficient q) (2*q+3) u]
    with n hn m B qlen Dlen hm hB hmn hBn hq hD
  have h := hn (height m B) (max qlen Dlen) (height_le n m B q hmn hBn) (max_le hq hD)
  calc
    (constructedBudget f g m B qlen Dlen:ℝ) ≤
        (envelope (fixedConstant f g) (height m B) (max qlen Dlen):ℝ) := by
      exact_mod_cast constructedBudget_le f g m B qlen Dlen hm hB
    _ ≤ _ := h

theorem eventually_constructedBudget_with_words (f g q : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀m B qlen Dlen:ℕ,
      0 < m → 0 < B → m ≤ n*B → B ≤ L n^q →
      (constructedBudget f g m B qlen Dlen:ℝ) ≤
        ((max qlen Dlen:ℕ)+1:ℝ)^6*(2:ℝ)^Statement.runtimeScale n := by
  filter_upwards [eventually_envelope_with_words (fixedConstant f g)
    (heightCoefficient q) (2*q+3)] with n hn m B qlen Dlen hm hB hmn hBn
  have h := hn (height m B) (max qlen Dlen) (height_le n m B q hmn hBn)
  calc
    (constructedBudget f g m B qlen Dlen:ℝ) ≤
        (envelope (fixedConstant f g) (height m B) (max qlen Dlen):ℝ) := by
      exact_mod_cast constructedBudget_le f g m B qlen Dlen hm hB
    _ ≤ _ := h

/-- The exact two fixed primitive-machine multipliers, already instantiated. -/
noncomputable def primitiveSearchBudget (m B qlen Dlen : ℕ) : ℕ :=
  constructedBudget
    (SubexponentialSAT.BitProgram.primitiveOverhead CodeSearchProgram.localProgram)
    (SubexponentialSAT.BitProgram.primitiveOverhead CodeSearchProgram.graphProgram)
    m B qlen Dlen

theorem eventually_primitiveSearchBudget (q u : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀m B qlen Dlen:ℕ,
      0 < m → 0 < B → m ≤ n*B → B ≤ L n^q →
      qlen ≤ (n+1)^u → Dlen ≤ (n+1)^u →
      (primitiveSearchBudget m B qlen Dlen:ℝ) ≤ (2:ℝ)^Statement.runtimeScale n :=
  eventually_constructedBudget _ _ q u

theorem eventually_primitiveSearchBudget_with_words (q : ℕ) :
    ∀ᶠ n:ℕ in atTop, ∀m B qlen Dlen:ℕ,
      0 < m → 0 < B → m ≤ n*B → B ≤ L n^q →
      (primitiveSearchBudget m B qlen Dlen:ℝ) ≤
        ((max qlen Dlen:ℕ)+1:ℝ)^6*(2:ℝ)^Statement.runtimeScale n :=
  eventually_constructedBudget_with_words _ _ q

end SubexponentialSAT.SqrtLog.CodeSetupCost

end OAI.Algorithms
