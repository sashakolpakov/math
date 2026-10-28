import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.QuantitativeSparsify
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyWorklist

namespace OAI.Algorithms

/-!
# Quantitative bounds for the executable list sparsifier

This module instantiates the actual list search and depth-first worklist at the
arithmetically selected inverse budget. The finite-set view of each output is
used only for SAT semantics. Node visits are counted by the actual worklist;
they are not presented as primitive bit-machine transitions.
-/

namespace SubexponentialSAT.ExecQuantitativeSparsify

open SAT

variable {n : ℕ}

abbrev Formula (n : ℕ) := ExecCNF.Formula (Literal (Fin n))

/-- The fixed syntactic order on the literals of a clause. -/
def literalList (C : Clause (Fin n)) : List (Literal (Fin n)) :=
  let r := fun a b : Literal (Fin n) => Encoding.literalCode a ≤ Encoding.literalCode b
  letI : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.literalCode_injective (le_antisymm h h')⟩
  C.sort r

/-- The fixed syntactic order on clauses, independent of their truth values. -/
def orderedClauses (F : CNF (Fin n)) : List (Clause (Fin n)) :=
  let r := fun C D : Clause (Fin n) => Encoding.clauseNumbers C ≤ Encoding.clauseNumbers D
  letI : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.clauseNumbers_injective (le_antisymm h h')⟩
  F.sort r

/-- A concrete list representation of the typed input formula. -/
def formulaList (F : CNF (Fin n)) : Formula n :=
  (orderedClauses F).map literalList

theorem literalList_codes (C : Clause (Fin n)) :
    (literalList C).map Encoding.literalCode = Encoding.clauseNumbers C := by
  let r := fun a b : Literal (Fin n) => Encoding.literalCode a ≤ Encoding.literalCode b
  let _ : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  let _ : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  let _ : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.literalCode_injective (le_antisymm h h')⟩
  unfold literalList Encoding.clauseNumbers
  let e : Literal (Fin n) ↪ ℕ := ⟨Encoding.literalCode, Encoding.literalCode_injective⟩
  have he : C.map e = C.image Encoding.literalCode := Finset.map_eq_image e C
  rw [← he]
  change (C.val.sort _).map Encoding.literalCode = (C.val.map Encoding.literalCode).sort _
  apply Multiset.map_sort
  intro a ha b hb
  rfl

theorem orderedClauses_codes (F : CNF (Fin n)) :
    (orderedClauses F).map Encoding.clauseNumbers = Encoding.cnfNumbers F := by
  let r := fun C D : Clause (Fin n) => Encoding.clauseNumbers C ≤ Encoding.clauseNumbers D
  let _ : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  let _ : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  let _ : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.clauseNumbers_injective (le_antisymm h h')⟩
  unfold orderedClauses Encoding.cnfNumbers
  let e : Clause (Fin n) ↪ List ℕ :=
    ⟨Encoding.clauseNumbers, Encoding.clauseNumbers_injective⟩
  have he : F.map e = F.image Encoding.clauseNumbers := Finset.map_eq_image e F
  rw [← he]
  change (F.val.sort _).map Encoding.clauseNumbers = (F.val.map Encoding.clauseNumbers).sort _
  apply Multiset.map_sort
  intro a ha b hb
  rfl

/-- The numerical payload of the executable input is exactly the canonical
payload specified by `Encoding`, including both sorting conventions. -/
theorem formulaList_codes (F : CNF (Fin n)) :
    (formulaList F).map (List.map Encoding.literalCode) = Encoding.cnfNumbers F := by
  simp only [formulaList, List.map_map, Function.comp_def, literalList_codes]
  exact orderedClauses_codes F

def encodeRawFormula (F : Formula n) : List Bool :=
  Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
    (F.map (List.map Encoding.literalCode))

theorem encode_formulaList (F : CNF (Fin n)) :
    encodeRawFormula (formulaList F) = Encoding.encodeCNFBody F := by
  rw [encodeRawFormula, formulaList_codes]
  rfl

theorem encodeCNF_formulaList (F : CNF (Fin n)) :
    Encoding.encodeNat n ++ encodeRawFormula (formulaList F) = Encoding.encodeCNF F := by
  rw [encode_formulaList]
  rfl

/-- The actual unary literal representation is bounded by the ambient variable
count; literal comparisons are not treated as constant-size operations. -/
theorem encodedLiteral_length_le (l : Literal (Fin n)) :
    (Encoding.encodeNat (Encoding.literalCode l)).length ≤ 2 * n + 1 := by
  rw [Encoding.length_encodeNat]
  have := Encoding.literalCode_lt l
  omega

theorem encodeRawClause_length_le (C : List (Literal (Fin n))) :
    (Encoding.encodeList Encoding.encodeNat (C.map Encoding.literalCode)).length ≤
      1 + (4 * n + 4) * C.length := by
  have h := Encoding.length_encodeList_upper Encoding.encodeNat
    (C.map Encoding.literalCode) (2 * n + 1) (by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
      exact encodedLiteral_length_le l)
  simpa only [List.length_map, show 2 * (2 * n + 1) + 2 = 4 * n + 4 by omega] using h

theorem encodeRawFormula_length_le (F : Formula n) (k : ℕ)
    (hF : ExecSunflowerSearch.RawWidthAtMost k F) :
    (encodeRawFormula F).length ≤ 1 + (4 + (8 * n + 8) * k) * F.length := by
  have h := Encoding.length_encodeList_upper (Encoding.encodeList Encoding.encodeNat)
    (F.map (List.map Encoding.literalCode)) (1 + (4 * n + 4) * k) (by
      intro C hC
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
      exact (encodeRawClause_length_le D).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hF D hD)) _))
  have hc : 2 * (1 + (4 * n + 4) * k) + 2 = 4 + (8 * n + 8) * k := by ring
  simpa only [encodeRawFormula, List.length_map, hc] using h

theorem raw_clause_count_le (F : Formula n) (k : ℕ)
    (hDistinct : (F.map ExecCNF.clauseSet).Nodup)
    (hF : ExecSunflowerSearch.RawWidthAtMost k F) : F.length ≤ (2 * n + 1) ^ k := by
  have hcard : (ExecCNF.formulaSet F).card = F.length := by
    simpa only [ExecCNF.formulaSet, List.length_map] using List.toFinset_card_of_nodup hDistinct
  rw [← hcard]
  exact QuantitativeSparsify.clause_count_le (ExecCNF.formulaSet F) k
    (ExecSparsifyWorklist.semantic_width_of_raw F k hF)

/-- Each normalized intermediate formula has polynomially many bits. The
displayed coefficient and degree depend only on the fixed clause width. -/
theorem encodeRawFormula_polynomial (F : Formula n) (k : ℕ)
    (hDistinct : (F.map ExecCNF.clauseSet).Nodup)
    (hF : ExecSunflowerSearch.RawWidthAtMost k F) :
    (encodeRawFormula F).length ≤ (8 * k + 5) * (n + 1) ^ (2 * k + 1) := by
  have hcard := raw_clause_count_le F k hDistinct hF
  have hbase : 2 * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hcoeff : 4 + (8 * n + 8) * k ≤ (8 * k + 4) * (n + 1) := by nlinarith
  calc
    (encodeRawFormula F).length ≤ 1 + (4 + (8 * n + 8) * k) * F.length :=
      encodeRawFormula_length_le F k hF
    _ ≤ 1 + ((8 * k + 4) * (n + 1)) * ((n + 1) ^ 2) ^ k :=
      Nat.add_le_add_left (Nat.mul_le_mul hcoeff
        (hcard.trans (Nat.pow_le_pow_left hbase k))) _
    _ = 1 + (8 * k + 4) * (n + 1) ^ (2 * k + 1) := by
      rw [← pow_mul, pow_succ]
      ring
    _ ≤ (8 * k + 5) * (n + 1) ^ (2 * k + 1) := by
      have hp : 1 ≤ (n + 1) ^ (2 * k + 1) := Nat.one_le_pow _ _ (by omega)
      nlinarith

@[simp] theorem literalList_set (C : Clause (Fin n)) :
    ExecCNF.clauseSet (literalList C) = C := by
  simp [ExecCNF.clauseSet, literalList]

@[simp] theorem literalList_length (C : Clause (Fin n)) :
    (literalList C).length = C.card := by simp [literalList]

@[simp] theorem mem_orderedClauses (F : CNF (Fin n)) (C : Clause (Fin n)) :
    C ∈ orderedClauses F ↔ C ∈ F := by simp [orderedClauses]

@[simp] theorem formulaList_set (F : CNF (Fin n)) :
    ExecCNF.formulaSet (formulaList F) = F := by
  ext C
  simp [ExecCNF.mem_formulaSet, formulaList]

@[simp] theorem formulaList_length (F : CNF (Fin n)) :
    (formulaList F).length = F.card := by simp [formulaList, orderedClauses]

theorem formulaList_width (F : CNF (Fin n)) (k : ℕ) (hF : WidthAtMost k F) :
    ExecSunflowerSearch.RawWidthAtMost k (formulaList F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
  simpa only [literalList_length] using hF D ((mem_orderedClauses F D).mp hD)

/-- Execute the list algorithm at the explicit threshold parameter. -/
def executeFor (M k : ℕ) (hM : 2 ≤ M) (F : Formula n) :
    ExecSparsifyWorklist.State (Formula n) :=
  ExecSparsifyWorklist.execute (SparsificationConstants.z M) k
    (fun d hd => SparsificationConstants.threshold_ge_two M d hM hd) F

/-- The output in the finite-set SAT interface, obtained from actual raw output. -/
def leavesFor (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n)) : List (CNF (Fin n)) :=
  ((executeFor M k hM (formulaList F)).leaves).map ExecCNF.formulaSet

theorem leavesFor_eval_iff (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n))
    (a : Assignment (Fin n)) :
    F.eval a = true ↔ ∃ G ∈ leavesFor M k hM F, G.eval a = true := by
  have h := ExecSparsifyWorklist.execute_models (SparsificationConstants.z M) k
    (fun d hd => SparsificationConstants.threshold_ge_two M d hM hd) (formulaList F) a
  rw [formulaList_set] at h
  rw [h]
  constructor
  · rintro ⟨G, hG, ha⟩
    exact ⟨ExecCNF.formulaSet G, List.mem_map.mpr ⟨G, hG, rfl⟩, ha⟩
  · rintro ⟨G, hG, ha⟩
    obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hG
    exact ⟨R, hR, ha⟩

theorem leavesFor_correct (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n)) :
    Satisfiable F ↔ ∃ G ∈ leavesFor M k hM F, Satisfiable G := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨G, hG, hGa⟩ := (leavesFor_eval_iff M k hM F a).mp ha
    exact ⟨G, hG, a, hGa⟩
  · rintro ⟨G, hG, a, ha⟩
    exact ⟨a, (leavesFor_eval_iff M k hM F a).mpr ⟨G, hG, ha⟩⟩

theorem leavesFor_width (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ leavesFor M k hM F, WidthAtMost k G := by
  intro G hG
  obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hG
  apply ExecSparsifyWorklist.execute_width _ _ _ (formulaList F) _ R hR
  simpa only [formulaList_set] using hF

theorem leavesFor_occurrence (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ leavesFor M k hM F,
      OccurrenceAtMost (SparsificationConstants.occurrenceCap M k) G := by
  intro G hG
  obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hG
  apply ExecSparsifyWorklist.execute_occurrence M k hM (formulaList F) _ R hR
  simpa only [formulaList_set] using hF

def chosenExecute (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : Formula n) :
    ExecSparsifyWorklist.State (Formula n) :=
  executeFor (SparsificationBudget.chooseM k hk s) k
    (SparsificationBudget.chooseM_ge_two k hk s) F

/-- Actual executable-list leaves at inverse budget s. -/
def chosenLeaves (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n)) :
    List (CNF (Fin n)) :=
  (chosenExecute k hk s (formulaList F)).leaves.map ExecCNF.formulaSet

theorem chosenLeaves_eval_iff (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n))
    (a : Assignment (Fin n)) :
    F.eval a = true ↔ ∃ G ∈ chosenLeaves k hk s F, G.eval a = true :=
  leavesFor_eval_iff _ _ _ F a

theorem chosenLeaves_correct (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n)) :
    Satisfiable F ↔ ∃ G ∈ chosenLeaves k hk s F, Satisfiable G :=
  leavesFor_correct _ _ _ F

theorem chosenLeaves_width (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ chosenLeaves k hk s F, WidthAtMost k G :=
  leavesFor_width _ _ _ F hF

theorem chosenLeaves_occurrence (k : ℕ) (hk : 2 ≤ k) (s : ℕ) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ chosenLeaves k hk s F,
      OccurrenceAtMost (QuantitativeSparsify.chosenOccurrenceBound k hk s) G :=
  leavesFor_occurrence _ _ _ F hF

/-- A uniform polynomial factor for the actual number of worklist visits.
The counted transition invokes the explicitly defined list search; a further
bit-program refinement must charge the operations inside that search. -/
theorem chosenExecute_visits_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ (s : ℕ) (_hs : 0 < s) {n : ℕ} (F : Formula n),
      ((chosenExecute k hk s F).visits : ℝ) ≤
        (A : ℝ) * ((s : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ ((n : ℝ) / s) := by
  have hp : SparsificationConstants.PolynomialBound (fun s =>
      (SparsificationConstants.C (SparsificationBudget.chooseM k hk s) (k - 1) + 1) *
        (k + 1)) :=
    ((SparsificationBudget.chosenC_polynomialBound k hk (k - 1)).add
      (SparsificationConstants.polynomialBound_const 1)).mul
        (SparsificationConstants.polynomialBound_const (k + 1))
  obtain ⟨A, q, hpoly⟩ := QuantitativeSparsify.polynomialBound_shift hp
  refine ⟨A, q, ?_⟩
  intro s hs n F
  let M := SparsificationBudget.chooseM k hk s
  have hM := SparsificationBudget.chooseM_ge_two k hk s
  have hspec := SparsificationBudget.chooseM_spec k hk s hs
  have h := ExecSparsifyWorklist.execute_visits_quantitative M k hM (by omega)
    ((1 : ℝ) / s) F hspec.ratio_le (hspec.logb_budget hk hs)
  have hc : ((SparsificationConstants.C M (k - 1) + 1 : ℕ) : ℝ) *
      ((k + 1 : ℕ) : ℝ) ≤ (A : ℝ) * ((s : ℝ) + 2) ^ q := by
    exact_mod_cast hpoly s
  have h' := h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
      (Real.rpow_nonneg (by norm_num) _))
  simpa only [chosenExecute, executeFor, M, one_div, inv_mul_eq_div] using h'

theorem chosenLeaves_length_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ (s : ℕ) (_hs : 0 < s) {n : ℕ} (F : CNF (Fin n)),
      ((chosenLeaves k hk s F).length : ℝ) ≤
        (A : ℝ) * ((s : ℝ) + 2) ^ q * ((n : ℝ) + 1) ^ 2 * (2 : ℝ) ^ ((n : ℝ) / s) := by
  obtain ⟨A, q, hbound⟩ := chosenExecute_visits_polynomial k hk
  refine ⟨A, q, ?_⟩
  intro s hs n F
  apply le_trans ?_ (hbound s hs (formulaList F))
  have h := ExecSparsifyWorklist.initial_run_leaves_length_le_visits
    (ExecSparsifyWorklist.executableBranching
      (SparsificationConstants.z (SparsificationBudget.chooseM k hk s)) k
      (fun d hd => SparsificationConstants.threshold_ge_two _ d
        (SparsificationBudget.chooseM_ge_two k hk s) hd))
    (ExecSparsifyWorklist.normalizedInput (formulaList F))
  simpa only [chosenLeaves, List.length_map] using (show
    (((chosenExecute k hk s (formulaList F)).leaves.length : ℕ) : ℝ) ≤
      ((chosenExecute k hk s (formulaList F)).visits : ℝ) by exact_mod_cast h)

/-- The rational interface first rounds the reciprocal budget; it never
raises numbers to powers proportional to an unreduced input denominator. -/
def sigmaExecute (k : ℕ) (hk : 2 ≤ k) (σ : ℚ) (F : Formula n) :
    ExecSparsifyWorklist.State (Formula n) :=
  chosenExecute k hk (SparsificationBudget.reciprocalIndex σ.num.natAbs σ.den) F

def sigmaLeaves (k : ℕ) (hk : 2 ≤ k) (σ : ℚ) (F : CNF (Fin n)) :
    List (CNF (Fin n)) :=
  chosenLeaves k hk (SparsificationBudget.reciprocalIndex σ.num.natAbs σ.den) F

theorem sigmaLeaves_eval_iff (k : ℕ) (hk : 2 ≤ k) (σ : ℚ) (F : CNF (Fin n))
    (a : Assignment (Fin n)) :
    F.eval a = true ↔ ∃ G ∈ sigmaLeaves k hk σ F, G.eval a = true :=
  chosenLeaves_eval_iff k hk _ F a

theorem sigmaLeaves_correct (k : ℕ) (hk : 2 ≤ k) (σ : ℚ) (F : CNF (Fin n)) :
    Satisfiable F ↔ ∃ G ∈ sigmaLeaves k hk σ F, Satisfiable G :=
  chosenLeaves_correct k hk _ F

theorem sigmaLeaves_width (k : ℕ) (hk : 2 ≤ k) (σ : ℚ) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ sigmaLeaves k hk σ F, WidthAtMost k G :=
  chosenLeaves_width k hk _ F hF

theorem sigmaLeaves_occurrence (k : ℕ) (hk : 2 ≤ k) (σ : ℚ) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ sigmaLeaves k hk σ F,
      OccurrenceAtMost
        (SparsificationConstants.occurrenceCap (SparsificationBudget.chooseForSigma k hk σ) k) G :=
  chosenLeaves_occurrence k hk _ F hF

theorem sigmaExecute_visits_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ (σ : ℚ), 0 < σ → σ ≤ 1 → ∀ {n : ℕ} (F : Formula n),
      ((sigmaExecute k hk σ F).visits : ℝ) ≤
        (A : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ q * ((n : ℝ) + 1) ^ 2 *
          (2 : ℝ) ^ ((σ : ℝ) * n) := by
  obtain ⟨A, q, hbound⟩ := chosenExecute_visits_polynomial k hk
  refine ⟨A * 2 ^ q, q, ?_⟩
  intro σ hσ hσone n F
  let s := SparsificationBudget.reciprocalIndex σ.num.natAbs σ.den
  have hs : 0 < s := by
    have := SparsificationBudget.reciprocalIndex_ge_two σ.num.natAbs σ.den
    dsimp [s]
    omega
  have hdata := SparsificationBudget.rational_num_data σ hσ
  have hInv : (σ.den : ℝ) / σ.num.natAbs = (σ : ℝ)⁻¹ := by
    rw [← hdata.2, inv_div]
  have hidx : (s : ℝ) ≤ (σ : ℝ)⁻¹ + 2 := by
    have h := SparsificationBudget.reciprocalIndex_le_inverse_add_two
      σ.num.natAbs σ.den hdata.1
    simpa only [s, hInv] using h
  have hsigma : 0 ≤ (σ : ℝ) := by exact_mod_cast hσ.le
  have hidx' : (s : ℝ) + 2 ≤ 2 * ((σ : ℝ)⁻¹ + 2) := by
    have hi := inv_nonneg.mpr hsigma
    linarith
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ (s : ℝ) + 2 by positivity) hidx' q
  have hpoly : (A : ℝ) * ((s : ℝ) + 2) ^ q ≤
      ((A * 2 ^ q : ℕ) : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ q := by
    calc
      (A : ℝ) * ((s : ℝ) + 2) ^ q ≤
          (A : ℝ) * (2 * ((σ : ℝ)⁻¹ + 2)) ^ q :=
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
      _ = ((A * 2 ^ q : ℕ) : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ q := by
        push_cast
        rw [mul_pow]
        ring
  have hbudget : (1 : ℝ) / s ≤ (σ : ℝ) := by
    have h := SparsificationBudget.reciprocalIndex_budget σ.num.natAbs σ.den hdata.1
      (SparsificationBudget.rational_num_le_den σ hσ hσone)
    simpa only [s, hdata.2] using h
  have hexp : (2 : ℝ) ^ ((n : ℝ) / s) ≤ (2 : ℝ) ^ ((σ : ℝ) * n) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa only [one_div, inv_mul_eq_div] using
      mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg n)
  have h := hbound s hs F
  exact h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hpoly (sq_nonneg _)) hexp
      (Real.rpow_nonneg (by norm_num) _) (by positivity))

theorem sigmaLeaves_length_polynomial (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q : ℕ, ∀ (σ : ℚ), 0 < σ → σ ≤ 1 → ∀ {n : ℕ} (F : CNF (Fin n)),
      ((sigmaLeaves k hk σ F).length : ℝ) ≤
        (A : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ q * ((n : ℝ) + 1) ^ 2 *
          (2 : ℝ) ^ ((σ : ℝ) * n) := by
  obtain ⟨A, q, hbound⟩ := sigmaExecute_visits_polynomial k hk
  refine ⟨A, q, ?_⟩
  intro σ hσ hσone n F
  apply le_trans ?_ (hbound σ hσ hσone (formulaList F))
  have h := ExecSparsifyWorklist.initial_run_leaves_length_le_visits
    (ExecSparsifyWorklist.executableBranching
      (SparsificationConstants.z (SparsificationBudget.chooseForSigma k hk σ)) k
      (fun d hd => SparsificationConstants.threshold_ge_two _ d
        (SparsificationBudget.chooseForSigma_ge_two k hk σ) hd))
    (ExecSparsifyWorklist.normalizedInput (formulaList F))
  simpa only [sigmaLeaves, chosenLeaves, sigmaExecute, List.length_map] using (show
    (((sigmaExecute k hk σ (formulaList F)).leaves.length : ℕ) : ℝ) ≤
      ((sigmaExecute k hk σ (formulaList F)).visits : ℝ) by exact_mod_cast h)

/-- The finite-output and incidence conclusions of quantitative sparsification
for every rational budget. The constants precede the budget and the input.
Primitive bit-runtime is a separate refinement obligation. -/
theorem sigmaLeaves_spec (k : ℕ) (hk : 2 ≤ k) :
    ∃ A q B d : ℕ, ∀ (σ : ℚ), 0 < σ → σ ≤ 1 → ∀ {n : ℕ} (F : CNF (Fin n)),
      WidthAtMost k F →
      (∀ a, F.eval a = true ↔ ∃ G ∈ sigmaLeaves k hk σ F, G.eval a = true) ∧
      (∀ G ∈ sigmaLeaves k hk σ F, WidthAtMost k G ∧
        OccurrenceAtMost
          (SparsificationConstants.occurrenceCap (SparsificationBudget.chooseForSigma k hk σ) k) G) ∧
      ((SparsificationConstants.occurrenceCap (SparsificationBudget.chooseForSigma k hk σ) k : ℕ) : ℝ)
        ≤ (B : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ d ∧
      ((sigmaLeaves k hk σ F).length : ℝ) ≤
        (A : ℝ) * ((σ : ℝ)⁻¹ + 2) ^ q * ((n : ℝ) + 1) ^ 2 *
          (2 : ℝ) ^ ((σ : ℝ) * n) := by
  obtain ⟨A, q, hcount⟩ := sigmaLeaves_length_polynomial k hk
  obtain ⟨B, d, hdegree⟩ := SparsificationBudget.sigmaOccurrenceCap_polynomial k hk
  refine ⟨A, q, B, d, ?_⟩
  intro σ hσ hσone n F hF
  exact ⟨sigmaLeaves_eval_iff k hk σ F,
    fun G hG => ⟨sigmaLeaves_width k hk σ F hF G hG,
      sigmaLeaves_occurrence k hk σ F hF G hG⟩,
    hdegree σ hσ, hcount σ hσ hσone F⟩

end SubexponentialSAT.ExecQuantitativeSparsify

end OAI.Algorithms
