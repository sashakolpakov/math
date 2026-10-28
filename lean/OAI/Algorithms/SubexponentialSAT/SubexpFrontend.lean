import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.StackEncoding

namespace OAI.Algorithms

/-!
# Syntactic frontend for the variable-parameter SAT algorithm

The external input declares `n` Boolean coordinates. We first normalize the
finite CNF, then enumerate only its syntactically appearing coordinates in
increasing order. The resulting coordinate set is retained through all later
branching; this frontend is not reapplied at sparsification leaves.

All constructions inspect finite syntax. No satisfiability test, choice of a
satisfying assignment, or noncomputable enumeration is used by `prepare`.
-/

namespace SubexponentialSAT.SubexpFrontend

open SAT

section Rename

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def renameLiteral (f : V → W) (l : Literal V) : Literal W :=
  ⟨f l.variable, l.positive⟩

def renameClause (f : V → W) (C : Clause V) : Clause W :=
  C.image (renameLiteral f)

def renameCNF (f : V → W) (F : CNF V) : CNF W :=
  F.image (renameClause f)

omit [DecidableEq V] [DecidableEq W] in
theorem renameLiteral_injective {f : V → W} (hf : Function.Injective f) :
    Function.Injective (renameLiteral f) := by
  rintro ⟨v, p⟩ ⟨w, q⟩ h
  have hv : v = w := hf (congrArg Literal.variable h)
  have hp : p = q := congrArg Literal.positive h
  cases hv
  cases hp
  rfl

omit [DecidableEq V] in
theorem renameClause_injective {f : V → W} (hf : Function.Injective f) :
    Function.Injective (renameClause f) :=
  Finset.image_injective (renameLiteral_injective hf)

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem eval_renameLiteral (f : V → W) (l : Literal V) (a : W → Bool) :
    (renameLiteral f l).eval a = l.eval (a ∘ f) := rfl

omit [DecidableEq V] in
@[simp] theorem eval_renameClause (f : V → W) (C : Clause V) (a : W → Bool) :
    (renameClause f C).eval a = C.eval (a ∘ f) := by
  apply Bool.eq_iff_iff.mpr
  simp [Clause.eval, renameClause, renameLiteral]

omit [DecidableEq V] in
@[simp] theorem eval_renameCNF (f : V → W) (F : CNF V) (a : W → Bool) :
    (renameCNF f F).eval a = F.eval (a ∘ f) := by
  apply Bool.eq_iff_iff.mpr
  simp [CNF.eval, renameCNF, Clause.eval, renameClause, renameLiteral]

omit [DecidableEq V] in
theorem renameClause_mono (f : V → W) {C D : Clause V} (h : C ⊆ D) :
    renameClause f C ⊆ renameClause f D := Finset.image_mono _ h

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem renameLiteral_negate (f : V → W) (l : Literal V) :
    renameLiteral f l.negate = (renameLiteral f l).negate := rfl

end Rename

/-- Explicit finite universe of signed literals, including the empty-variable case. -/
def allLiterals (n : ℕ) : Finset (Literal (Fin n)) :=
  (Finset.univ : Finset (Fin n × Bool)).image fun x => ⟨x.1, x.2⟩

@[simp] theorem mem_allLiterals {n : ℕ} (l : Literal (Fin n)) : l ∈ allLiterals n := by
  rcases l with ⟨v, p⟩
  exact Finset.mem_image.mpr ⟨(v, p), Finset.mem_univ _, rfl⟩

theorem card_allLiterals (n : ℕ) : (allLiterals n).card = 2 * n := by
  have hi : Function.Injective (fun x : Fin n × Bool => (⟨x.1, x.2⟩ : Literal (Fin n))) := by
    rintro ⟨v, p⟩ ⟨w, q⟩ h
    exact Prod.ext (congrArg Literal.variable h) (congrArg Literal.positive h)
  simp [allLiterals, Finset.card_image_of_injective _ hi, Nat.mul_comm]

/-- Pull a clause back along a variable map by scanning the finite new literal universe. -/
def pullClause {n m : ℕ} (f : Fin m → Fin n) (C : Clause (Fin n)) : Clause (Fin m) :=
  (allLiterals m).filter fun l => renameLiteral f l ∈ C

@[simp] theorem mem_pullClause {n m : ℕ} (f : Fin m → Fin n)
    (C : Clause (Fin n)) (l : Literal (Fin m)) :
    l ∈ pullClause f C ↔ renameLiteral f l ∈ C := by
  simp [pullClause]

theorem rename_pullClause_subset {n m : ℕ} (f : Fin m → Fin n) (C : Clause (Fin n)) :
    renameClause f (pullClause f C) ⊆ C := by
  intro l hl
  obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hl
  exact (mem_pullClause f C l').mp hl'

theorem rename_pullClause {n m : ℕ} (f : Fin m → Fin n) (C : Clause (Fin n))
    (hcover : ∀ l ∈ C, ∃ v, f v = l.variable) :
    renameClause f (pullClause f C) = C := by
  apply Finset.Subset.antisymm (rename_pullClause_subset f C)
  intro l hl
  obtain ⟨v, hv⟩ := hcover l hl
  have he : renameLiteral f ⟨v, l.positive⟩ = l := by
    rcases l with ⟨w, p⟩
    simp only [renameLiteral] at *
    cases hv
    rfl
  exact Finset.mem_image.mpr
    ⟨⟨v, l.positive⟩, (mem_pullClause f C _).mpr (he ▸ hl), he⟩

theorem pullClause_card_le {n m : ℕ} (f : Fin m → Fin n)
    (hf : Function.Injective f) (C : Clause (Fin n)) :
    (pullClause f C).card ≤ C.card := by
  calc
    (pullClause f C).card = (renameClause f (pullClause f C)).card :=
      (Finset.card_image_of_injective _ (renameLiteral_injective hf)).symm
    _ ≤ C.card := Finset.card_le_card (rename_pullClause_subset f C)

/-- The variables appearing in an explicit finite formula. -/
def appearing {n : ℕ} (F : CNF (Fin n)) : Finset (Fin n) :=
  F.biUnion fun C => C.image Literal.variable

@[simp] theorem mem_appearing {n : ℕ} (F : CNF (Fin n)) (v : Fin n) :
    v ∈ appearing F ↔ ∃ C ∈ F, ∃ l ∈ C, l.variable = v := by
  simp [appearing]

theorem literal_variable_mem {n : ℕ} {F : CNF (Fin n)} {C : Clause (Fin n)}
    (hC : C ∈ F) {l : Literal (Fin n)} (hl : l ∈ C) : l.variable ∈ appearing F :=
  (mem_appearing F l.variable).mpr ⟨C, hC, l, hl, rfl⟩

theorem appearing_mono {n : ℕ} {F G : CNF (Fin n)} (h : F ⊆ G) :
    appearing F ⊆ appearing G := by
  intro v hv
  obtain ⟨C, hC, l, hl, rfl⟩ := (mem_appearing F v).mp hv
  exact literal_variable_mem (h hC) hl

theorem appearing_card_le {n : ℕ} (F : CNF (Fin n)) : (appearing F).card ≤ n := by
  simpa using Finset.card_le_univ (appearing F)

theorem appearing_card_le_width_mul_card {n k : ℕ} (F : CNF (Fin n))
    (h : WidthAtMost k F) : (appearing F).card ≤ k * F.card := by
  calc
    (appearing F).card ≤ ∑ C ∈ F, (C.image Literal.variable).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ C ∈ F, C.card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ ≤ ∑ _C ∈ F, k := Finset.sum_le_sum (fun C hC => h C hC)
    _ = k * F.card := by simp [Nat.mul_comm]

/-- Increasing enumeration, implemented by finite sorting and index lookup. -/
def activeEquiv {n : ℕ} (F : CNF (Fin n)) :
    Fin (appearing F).card ≃o {v // v ∈ appearing F} :=
  (appearing F).orderIsoOfFin rfl

def oldVariable {n : ℕ} (F : CNF (Fin n)) (v : Fin (appearing F).card) : Fin n :=
  (activeEquiv F v).val

theorem oldVariable_injective {n : ℕ} (F : CNF (Fin n)) :
    Function.Injective (oldVariable F) := by
  intro u v h
  apply (activeEquiv F).injective
  exact Subtype.ext h

theorem oldVariable_mem {n : ℕ} (F : CNF (Fin n)) (v : Fin (appearing F).card) :
    oldVariable F v ∈ appearing F := (activeEquiv F v).property

theorem oldVariable_covers {n : ℕ} {F : CNF (Fin n)} {C : Clause (Fin n)}
    (hC : C ∈ F) (l : Literal (Fin n)) (hl : l ∈ C) :
    ∃ v, oldVariable F v = l.variable := by
  let x : {v // v ∈ appearing F} := ⟨l.variable, literal_variable_mem hC hl⟩
  refine ⟨(activeEquiv F).symm x, ?_⟩
  simp [oldVariable, x]

/-- Dense renaming, without another semantic simplification. -/
def compress {n : ℕ} (F : CNF (Fin n)) : CNF (Fin (appearing F).card) :=
  F.image (pullClause (oldVariable F))

theorem rename_compress {n : ℕ} (F : CNF (Fin n)) :
    renameCNF (oldVariable F) (compress F) = F := by
  apply Finset.Subset.antisymm
  · intro C hC
    obtain ⟨D, hD, hDC⟩ := Finset.mem_image.mp hC
    obtain ⟨E, hE, hED⟩ := Finset.mem_image.mp hD
    rw [← hDC, ← hED, rename_pullClause _ _ (oldVariable_covers hE)]
    exact hE
  · intro C hC
    apply Finset.mem_image.mpr
    refine ⟨pullClause (oldVariable F) C, Finset.mem_image.mpr ⟨C, hC, rfl⟩, ?_⟩
    exact rename_pullClause _ _ (oldVariable_covers hC)

/-- Evaluation commutes with the inverse coordinate map. -/
theorem eval_compress {n : ℕ} (F : CNF (Fin n)) (a : Fin n → Bool) :
    (compress F).eval (a ∘ oldVariable F) = F.eval a := by
  rw [← eval_renameCNF, rename_compress]

/-- Extend an assignment to the old declared coordinates, setting unused ones false. -/
def extendAssignment {n : ℕ} (F : CNF (Fin n))
    (a : Fin (appearing F).card → Bool) : Fin n → Bool :=
  fun v => if h : v ∈ appearing F then a ((activeEquiv F).symm ⟨v, h⟩) else false

@[simp] theorem extendAssignment_oldVariable {n : ℕ} (F : CNF (Fin n))
    (a : Fin (appearing F).card → Bool) (v : Fin (appearing F).card) :
    extendAssignment F a (oldVariable F v) = a v := by
  simp only [extendAssignment, dite_eq_left (oldVariable_mem F v)]
  have h : (⟨oldVariable F v, oldVariable_mem F v⟩ : {v // v ∈ appearing F}) =
      activeEquiv F v := rfl
  rw [h, OrderIso.symm_apply_apply]

theorem satisfiable_compress {n : ℕ} (F : CNF (Fin n)) :
    Satisfiable (compress F) ↔ Satisfiable F := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨extendAssignment F a, ?_⟩
    rw [← eval_compress]
    have h : extendAssignment F a ∘ oldVariable F = a := by
      funext v
      exact extendAssignment_oldVariable F a v
    rw [h]
    exact ha
  · rintro ⟨a, ha⟩
    exact ⟨a ∘ oldVariable F, (eval_compress F a).trans ha⟩

theorem compress_card_le {n : ℕ} (F : CNF (Fin n)) : (compress F).card ≤ F.card :=
  Finset.card_image_le

theorem width_compress {n k : ℕ} {F : CNF (Fin n)} (h : WidthAtMost k F) :
    WidthAtMost k (compress F) := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
  exact (pullClause_card_le _ (oldVariable_injective F) D).trans (h D hD)

theorem appearing_compress {n : ℕ} (F : CNF (Fin n)) :
    appearing (compress F) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  obtain ⟨C, hC, l, hl, hvar⟩ :=
    (mem_appearing F (oldVariable F v)).mp (oldVariable_mem F v)
  apply (mem_appearing (compress F) v).mpr
  refine ⟨pullClause (oldVariable F) C, Finset.mem_image.mpr ⟨C, hC, rfl⟩,
    ⟨v, l.positive⟩, ?_, rfl⟩
  apply (mem_pullClause _ _ _).mpr
  have he : renameLiteral (oldVariable F) ⟨v, l.positive⟩ = l := by
    rcases l with ⟨w, p⟩
    simp only at hvar
    simp [renameLiteral, hvar]
  exact he ▸ hl

/-- The number of coordinates retained by the actual frontend. -/
def numVariables {n : ℕ} (F : CNF (Fin n)) : ℕ :=
  (appearing (SAT.normalize F)).card

/-- Canonical preprocessing. The first component is the post-normalization
appearing-variable count, not the possibly larger declared input count. -/
def prepare {n : ℕ} (F : CNF (Fin n)) : (m : ℕ) × CNF (Fin m) :=
  ⟨numVariables F, compress (SAT.normalize F)⟩

theorem prepare_satisfiable {n : ℕ} (F : CNF (Fin n)) :
    Satisfiable (prepare F).2 ↔ Satisfiable F :=
  (satisfiable_compress (SAT.normalize F)).trans (SAT.satisfiable_normalize F)

theorem prepare_numVariables_le {n : ℕ} (F : CNF (Fin n)) : (prepare F).1 ≤ n :=
  appearing_card_le _

theorem prepare_card_le {n : ℕ} (F : CNF (Fin n)) : (prepare F).2.card ≤ F.card :=
  (compress_card_le (SAT.normalize F)).trans (Finset.card_le_card (SAT.normalize_subset F))

theorem prepare_width {n k : ℕ} {F : CNF (Fin n)} (h : WidthAtMost k F) :
    WidthAtMost k (prepare F).2 :=
  width_compress (SAT.widthAtMost_of_subset (SAT.normalize_subset F) h)

theorem prepare_all_variables_appear {n : ℕ} (F : CNF (Fin n)) :
    appearing (prepare F).2 = Finset.univ :=
  appearing_compress _

theorem prepare_not_tautology {n : ℕ} {F : CNF (Fin n)}
    {C : Clause (Fin (prepare F).1)} (hC : C ∈ (prepare F).2) : ¬ C.IsTautology := by
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
  rintro ⟨l, hl, hn⟩
  apply SAT.normalize_not_tautology hD
  refine ⟨renameLiteral (oldVariable (SAT.normalize F)) l,
    (mem_pullClause _ _ _).mp hl, ?_⟩
  have hn' := (mem_pullClause _ _ _).mp hn
  change renameLiteral (oldVariable (SAT.normalize F)) l.negate ∈ D
  exact hn'

theorem prepare_antichain {n : ℕ} {F : CNF (Fin n)}
    {C D : Clause (Fin (prepare F).1)}
    (hC : C ∈ (prepare F).2) (hD : D ∈ (prepare F).2) (hDC : D ⊆ C) : D = C := by
  obtain ⟨E, hE, hEC⟩ := Finset.mem_image.mp hC
  obtain ⟨G, hG, hGD⟩ := Finset.mem_image.mp hD
  subst C
  subst D
  have hGE := renameClause_mono (oldVariable (SAT.normalize F)) hDC
  rw [rename_pullClause _ _ (oldVariable_covers hG),
    rename_pullClause _ _ (oldVariable_covers hE)] at hGE
  have heq := SAT.normalize_antichain hE hG hGE
  rw [heq]

theorem prepare_numVariables_le_width_mul_card {n k : ℕ} (F : CNF (Fin n))
    (h : WidthAtMost k F) : (prepare F).1 ≤ k * F.card := by
  have hn := SAT.widthAtMost_of_subset (SAT.normalize_subset F) h
  exact (appearing_card_le_width_mul_card (SAT.normalize F) hn).trans
    (Nat.mul_le_mul_left k (Finset.card_le_card (SAT.normalize_subset F)))

theorem prepare_numVariables_le_inputLength {n : ℕ} (F : CNF (Fin n)) :
    (prepare F).1 ≤ Encoding.formulaBitLength F :=
  (prepare_numVariables_le F).trans (Encoding.numVariables_le_formulaBitLength F)

theorem prepare_card_le_inputLength {n : ℕ} (F : CNF (Fin n)) :
    (prepare F).2.card ≤ Encoding.formulaBitLength F :=
  (prepare_card_le F).trans (Encoding.numClauses_le_formulaBitLength F)

/-- No answer bits are attached: the prepared input is exactly the existing
canonical structural encoding. -/
def prepareCode {n : ℕ} (F : CNF (Fin n)) : List Bool :=
  Encoding.encodeFormula (prepare F)

/-- Signed literal codes are `2 * index + polarity`, matching the parser and
finite-list sparsifier interface. -/
def prepareNumbers {n : ℕ} (F : CNF (Fin n)) : List (List ℕ) :=
  Encoding.cnfNumbers (prepare F).2

theorem prepareNumbers_length {n : ℕ} (F : CNF (Fin n)) :
    (prepareNumbers F).length = (prepare F).2.card :=
  Encoding.length_cnfNumbers _

theorem prepareNumbers_clause_length {n k : ℕ} (F : CNF (Fin n))
    (h : WidthAtMost k F) {xs : List ℕ} (hx : xs ∈ prepareNumbers F) : xs.length ≤ k := by
  have hi : xs ∈ (prepare F).2.image Encoding.clauseNumbers := by
    simpa [prepareNumbers, Encoding.cnfNumbers] using hx
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hi
  rw [Encoding.length_clauseNumbers]
  exact prepare_width h C hC

theorem prepareNumbers_literal_lt {n : ℕ} (F : CNF (Fin n))
    {xs : List ℕ} (hx : xs ∈ prepareNumbers F) {c : ℕ} (hc : c ∈ xs) :
    c < 2 * (prepare F).1 := by
  have hi : xs ∈ (prepare F).2.image Encoding.clauseNumbers := by
    simpa [prepareNumbers, Encoding.cnfNumbers] using hx
  obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hi
  exact Encoding.mem_clauseNumbers_lt hc

/-- Executable semantics for the existing signed natural-number literal code. -/
def codeTruth (a : ℕ → Bool) (c : ℕ) : Bool :=
  a (c / 2) == decide (c % 2 = 1)

/-- Flip the polarity bit, retaining the variable index. -/
def negateCode (c : ℕ) : ℕ :=
  2 * (c / 2) + if c % 2 = 1 then 0 else 1

theorem codeTruth_negateCode (a : ℕ → Bool) (c : ℕ) :
    codeTruth a (negateCode c) = !(codeTruth a c) := by
  have hd0 : (2 * (c / 2)) / 2 = c / 2 := by omega
  have hd1 : (2 * (c / 2) + 1) / 2 = c / 2 := by omega
  have hm0 : (2 * (c / 2)) % 2 = 0 := by omega
  have hm1 : (2 * (c / 2) + 1) % 2 = 1 := by omega
  by_cases h : c % 2 = 1 <;> cases ha : a (c / 2) <;>
    simp [negateCode, codeTruth, h, hd0, hd1, hm0, hm1, ha]

theorem negateCode_negateCode (c : ℕ) : negateCode (negateCode c) = c := by
  have hd0 : (2 * (c / 2)) / 2 = c / 2 := by omega
  have hd1 : (2 * (c / 2) + 1) / 2 = c / 2 := by omega
  have hm0 : (2 * (c / 2)) % 2 = 0 := by omega
  have hm1 : (2 * (c / 2) + 1) % 2 = 1 := by omega
  by_cases h : c % 2 = 1
  · simp only [negateCode, h, ite_true, Nat.add_zero, hm0, Nat.zero_ne_one,
      ite_false, hd0]
    omega
  · have hr : c % 2 = 0 := by omega
    simp only [negateCode, h, ite_false, hm1, ite_true, hd1, Nat.add_zero]
    omega

theorem literalCode_negate {n : ℕ} (l : Literal (Fin n)) :
    Encoding.literalCode l.negate = negateCode (Encoding.literalCode l) := by
  rcases l with ⟨v, p⟩
  have hd0 : (2 * v.val) / 2 = v.val := by omega
  have hd1 : (2 * v.val + 1) / 2 = v.val := by omega
  have hm0 : (2 * v.val) % 2 = 0 := by omega
  have hm1 : (2 * v.val + 1) % 2 = 1 := by omega
  cases p <;> simp [Encoding.literalCode, Literal.negate, negateCode,
    hd0, hd1, hm0, hm1]

theorem codeTruth_literalCode {n : ℕ} (a : ℕ → Bool) (l : Literal (Fin n)) :
    codeTruth a (Encoding.literalCode l) = l.eval (fun v => a v.val) := by
  rcases l with ⟨v, p⟩
  have hdiv0 : (2 * v.val) / 2 = v.val := by omega
  have hdiv1 : (2 * v.val + 1) / 2 = v.val := by omega
  have hmod0 : (2 * v.val) % 2 = 0 := by omega
  have hmod1 : (2 * v.val + 1) % 2 = 1 := by omega
  cases p <;> simp [codeTruth, Encoding.literalCode, Literal.eval,
    hdiv0, hdiv1, hmod0, hmod1]

def evalNumberClause (a : ℕ → Bool) (xs : List ℕ) : Bool :=
  xs.any (codeTruth a)

def evalNumberCNF (a : ℕ → Bool) (xs : List (List ℕ)) : Bool :=
  xs.all (evalNumberClause a)

theorem evalNumberClause_clauseNumbers {n : ℕ} (a : ℕ → Bool)
    (C : Clause (Fin n)) :
    evalNumberClause a (Encoding.clauseNumbers C) = C.eval (fun v => a v.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [evalNumberClause, List.any_eq_true, Encoding.clauseNumbers,
    Finset.mem_sort, Finset.mem_image, Clause.eval_eq_true]
  constructor
  · rintro ⟨c, ⟨l, hl, rfl⟩, h⟩
    exact ⟨l, hl, (codeTruth_literalCode a l) ▸ h⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨Encoding.literalCode l, ⟨l, hl, rfl⟩,
      (codeTruth_literalCode a l).symm ▸ h⟩

theorem evalNumberCNF_cnfNumbers {n : ℕ} (a : ℕ → Bool) (F : CNF (Fin n)) :
    evalNumberCNF a (Encoding.cnfNumbers F) = F.eval (fun v => a v.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [evalNumberCNF, List.all_eq_true, Encoding.cnfNumbers,
    Finset.mem_sort, Finset.mem_image, CNF.eval_eq_true]
  constructor
  · intro h C hC
    exact (evalNumberClause_clauseNumbers a C) ▸ h _ ⟨C, hC, rfl⟩
  · intro h xs hxs
    obtain ⟨C, hC, rfl⟩ := hxs
    exact (evalNumberClause_clauseNumbers a C).symm ▸ h C hC

theorem prepareNumbers_eval {n : ℕ} (F : CNF (Fin n)) (a : ℕ → Bool) :
    evalNumberCNF a (prepareNumbers F) = (prepare F).2.eval (fun v => a v.val) :=
  evalNumberCNF_cnfNumbers a _

theorem prepareNumbers_satisfiable {n : ℕ} (F : CNF (Fin n)) :
    (∃ a : ℕ → Bool, evalNumberCNF a (prepareNumbers F) = true) ↔ Satisfiable F := by
  constructor
  · rintro ⟨a, ha⟩
    apply (prepare_satisfiable F).mp
    exact ⟨fun v => a v.val, (prepareNumbers_eval F a) ▸ ha⟩
  · intro h
    obtain ⟨a, ha⟩ := (prepare_satisfiable F).mpr h
    let e : ℕ → Bool := fun v => if h : v < (prepare F).1 then a ⟨v, h⟩ else false
    refine ⟨e, ?_⟩
    rw [prepareNumbers_eval]
    have he : (fun v : Fin (prepare F).1 => e v.val) = a := by
      funext v
      exact dite_eq_left v.isLt
    rw [he]
    exact ha

/-- Later sparsification leaves use this fixed coordinate type, even if some
coordinates stop appearing. It deliberately does not recompute `numVariables`. -/
abbrev RetainedCNF {n : ℕ} (F : CNF (Fin n)) := CNF (Fin (prepare F).1)

theorem retained_header {n : ℕ} (F : CNF (Fin n)) (G : RetainedCNF F) :
    Encoding.readNat (Encoding.encodeCNF G) =
      some ((prepare F).1, Encoding.encodeCNFBody G) :=
  Encoding.readNat_encodeCNF G

/-- Direct syntactic exits: reject an empty clause, accept an empty formula. -/
def shortcut {n : ℕ} (F : CNF (Fin n)) : Option Bool :=
  if (∅ : Clause (Fin n)) ∈ F then some false
  else if F = ∅ then some true else none

theorem shortcut_false_iff {n : ℕ} (F : CNF (Fin n)) :
    shortcut F = some false ↔ (∅ : Clause (Fin n)) ∈ F := by
  by_cases h : (∅ : Clause (Fin n)) ∈ F <;> simp [shortcut, h]

theorem shortcut_true_iff {n : ℕ} (F : CNF (Fin n)) :
    shortcut F = some true ↔ F = ∅ := by
  by_cases h : (∅ : Clause (Fin n)) ∈ F
  · have hn : F ≠ ∅ := by
      intro hF
      subst F
      simp at h
    simp [shortcut, h, hn]
  · simp [shortcut, h]

theorem shortcut_correct {n : ℕ} (F : CNF (Fin n)) (b : Bool)
    (h : shortcut F = some b) : b = true ↔ Satisfiable F := by
  cases b with
  | false =>
      have hn := SAT.not_satisfiable_of_empty_mem ((shortcut_false_iff F).mp h)
      simp [hn]
  | true =>
      have hF := (shortcut_true_iff F).mp h
      subst F
      simp [SAT.satisfiable_empty]

theorem clause_fin_zero_eq_empty (C : Clause (Fin 0)) : C = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨l, _⟩
  exact Fin.elim0 l.variable

theorem shortcut_complete_of_zero {n : ℕ} (F : CNF (Fin n)) (hn : n = 0) :
    ∃ b, shortcut F = some b := by
  subst n
  by_cases he : (∅ : Clause (Fin 0)) ∈ F
  · exact ⟨false, (shortcut_false_iff F).mpr he⟩
  · have hF : F = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨C, hC⟩
      exact he ((clause_fin_zero_eq_empty C) ▸ hC)
    exact ⟨true, (shortcut_true_iff F).mpr hF⟩

theorem prepare_shortcut_correct {n : ℕ} (F : CNF (Fin n)) (b : Bool)
    (h : shortcut (prepare F).2 = some b) : b = true ↔ Satisfiable F :=
  (shortcut_correct (prepare F).2 b h).trans (prepare_satisfiable F)

theorem prepare_shortcut_complete_of_zero {n : ℕ} (F : CNF (Fin n))
    (h : (prepare F).1 = 0) : ∃ b, shortcut (prepare F).2 = some b :=
  shortcut_complete_of_zero (prepare F).2 h

@[simp] theorem prepareCode_length {n : ℕ} (F : CNF (Fin n)) :
    (prepareCode F).length = Encoding.formulaBitLength (prepare F).2 := rfl

/-- The actual output encoding is bounded by a fixed polynomial in input
length and width. This is a length bound, not a machine runtime claim. -/
theorem prepareCode_length_le {n k : ℕ} (F : CNF (Fin n)) (h : WidthAtMost k F) :
    (prepareCode F).length ≤ Encoding.formulaBitLength F + 2 +
      (4 + (8 * Encoding.formulaBitLength F + 8) * k) * Encoding.formulaBitLength F := by
  let L := Encoding.formulaBitLength F
  have hm : (prepare F).1 ≤ L := prepare_numVariables_le_inputLength F
  have hc : (prepare F).2.card ≤ L := prepare_card_le_inputLength F
  have hcoef : 4 + (8 * (prepare F).1 + 8) * k ≤ 4 + (8 * L + 8) * k :=
    Nat.add_le_add_left (Nat.mul_le_mul_right k
      (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hm) 8)) 4
  exact (Encoding.formulaBitLength_upper (prepare F).2 (prepare_width h)).trans
    (Nat.add_le_add (Nat.add_le_add_right hm 2) (Nat.mul_le_mul hcoef hc))

/-- Standard polynomial-overhead shape for composition with the solver's
input-length bound: coefficient `8*k+8` and fixed degree two. -/
theorem prepareCode_length_quadratic {n k : ℕ} (F : CNF (Fin n))
    (h : WidthAtMost k F) :
    (prepareCode F).length + 1 ≤
      (8 * k + 8) * (Encoding.formulaBitLength F + 1) ^ 2 := by
  let L := Encoding.formulaBitLength F
  have hsmall : 5 * L + 3 ≤ 8 * ((L + 1) * (L + 1)) :=
    (show 5 * L + 3 ≤ 8 * (L + 1) by omega).trans
      (Nat.mul_le_mul_left 8 (Nat.le_mul_self (L + 1)))
  calc
    (prepareCode F).length + 1 ≤ L + 2 + (4 + (8 * L + 8) * k) * L + 1 :=
      Nat.add_le_add_right (prepareCode_length_le F h) 1
    _ = 8 * k * L * (L + 1) + (5 * L + 3) := by ring
    _ ≤ 8 * k * (L + 1) * (L + 1) + 8 * ((L + 1) * (L + 1)) :=
      Nat.add_le_add
        (Nat.mul_le_mul_right (L + 1)
          (Nat.mul_le_mul_left (8 * k) (Nat.le_succ L))) hsmall
    _ = (8 * k + 8) * (L + 1) ^ 2 := by ring

/-- Raw Boolean program input is already a width-one stack encoding. -/
@[simp] theorem prepareCode_stack {n : ℕ} (F : CNF (Fin n)) :
    StackEncoding.encodeDataStack StackEncoding.boolCode (prepareCode F) = prepareCode F :=
  StackEncoding.encodeDataStack_boolCode _

@[simp] theorem prepareCode_tape {n : ℕ} (F : CNF (Fin n)) :
    StackEncoding.tapeWord StackEncoding.boolCode (prepareCode F) = (prepareCode F).map some :=
  StackEncoding.tapeWord_boolCode _

end SubexponentialSAT.SubexpFrontend

end OAI.Algorithms
