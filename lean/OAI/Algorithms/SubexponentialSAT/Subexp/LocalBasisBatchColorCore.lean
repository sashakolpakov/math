import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchMatrix
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchSearchBounds

namespace OAI.Algorithms

/-! One actual matrix/search/serialization step in the local-basis batch. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls

def colorTail : Code := .seq buildMatrix (.seq runSearch finishSearch)

def measuredPort (j : Fin 128) : Prop := j.val < 119 ∨ 123 ≤ j.val

theorem matrixInputs_bounds (pair : Fin 128 × Fin 128) (hp : pair ∈ matrixInputs) :
    107 ≤ pair.1.val ∧ pair.1.val < 119 ∧ pair.2.val < 65 := by
  simp only [matrixInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem matrixCopyCost_le (a : Data) (B : ℕ)
    (hm : ∀ j, measuredPort j → (a.stacks j).length ≤ B) :
    copyManyCost matrixInputs a ≤ 70 * B + 50 := by
  have hd : ∀ p ∈ matrixInputs, ∀ q ∈ matrixInputs, p.1 ≠ q.2 := by
    intro p hp q hq he
    have h0 := matrixInputs_bounds p hp
    have h1 := matrixInputs_bounds q hq
    have hv := congrArg Fin.val he
    omega
  have hc := copyManyCost_le matrixInputs a B hd (by
    intro pair hp
    exact hm _ (Or.inl (matrixInputs_bounds pair hp).2.1))
  have hlen : matrixInputs.length = 10 := rfl
  rw [hlen] at hc
  omega

theorem searchInputs_measured (pair : Fin 128 × Fin 128) (hp : pair ∈ searchInputs) :
    measuredPort pair.1 := by
  simp only [searchInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    unfold measuredPort <;> decide

noncomputable def colorTailBudget (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (coefficients alphabet : List (ZMod p)) (E B : ℕ) : ℕ :=
  1000000000 * (B + ConstraintMatrixProgram.budget (Δ := Δ) p hr hQ t g coefficients E +
    BlockSearchExecution.cost (BlockSearchPredicate.scalarCode p) alphabet
      (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length
      (BlockCoefficientProgram.coefficientCost p
        (ConstraintMatrixProgram.rowList (Δ := Δ) hr hQ t g).length
        (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length) + 1)

theorem colorTail_eval (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (h2 : (2 : ZMod p) ≠ 0) (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (coefficients alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet) (E B : ℕ)
    (hE : ∀ i : Fin Δ, ∀ u ∈ ConstraintMatrixProgram.rows hr hQ t g i,
      ∀ y ∈ ConstraintMatrixProgram.columns hr hQ t g,
        ConstraintEntryProgram.programBudget p i t u y coefficients ≤ E)
    (base a : Data)
    (ready : MatrixReady p r Q Δ t.val g.val coefficients
      (TypeEnumeration.sideBytes r Q Δ t.val g.val) a)
    (halphabet : a.stacks 116 = ProgramEncoding.encodeRecords
      (alphabet.map (BlockSearchPredicate.scalarCode p).block))
    (hbank : ∀ i, a.stacks (searchPorts i) = [])
    (hbase : ∀ j : Fin 128, j.val < 107 ∨ j = 123 ∨ j = 124 → base.stacks j = [])
    (h126 : base.stacks 126 = [])
    (hhigh : ∀ j : Fin 128, 107 ≤ j.val → a.stacks j =
      Function.update (Function.update base.stacks 123
        (List.replicate (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length true)) 124
        (List.replicate ((TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length *
          (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length) true) j)
    (hsize : ∀ j, measuredPort j → (a.stacks j).length ≤ B) :
    let N := (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length
    ∃ (steps : ℕ) (b : Data) (C : Fin N → Fin N → ZMod p) (d : Fin (N + 1)),
      steps ≤ colorTailBudget (Δ := Δ) p hr hQ t g coefficients alphabet E B ∧
      Eval colorTail steps a b ∧
      BlockSearch.GoodPair (ConstraintMatrixProgram.matrix (Δ := Δ) p hr hQ t g coefficients)
        (BlockSearchEncoding.splitPair d C) ∧
      b.stacks = Function.update (Function.update base.stacks 122
        ((true :: Encoding.frame (resultPayload (List.replicate N true)
          (List.replicate d.val true) (BlockCoefficientProgram.tableBits p C))).reverse ++
            base.stacks 122)) 118 (true :: base.stacks 118) := by
  dsimp only
  let N := (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length
  let m := (ConstraintMatrixProgram.rowList (Δ := Δ) hr hQ t g).length
  let M := ConstraintMatrixProgram.matrix (Δ := Δ) p hr hQ t g coefficients
  let matrixBudget := ConstraintMatrixProgram.budget (Δ := Δ) p hr hQ t g coefficients E
  let searchBudget := BlockSearchExecution.cost (BlockSearchPredicate.scalarCode p) alphabet N
    (BlockCoefficientProgram.coefficientCost p m N)
  obtain ⟨nm, am, hnm, hem, hm0, hm55, hmhigh, hmregs⟩ :=
    buildMatrix_eval p h2 hr hQ t g coefficients E hE a ready
  have hnm' : nm ≤ 70 * B + 50 + matrixBudget := by
    have hc := matrixCopyCost_le a B hsize
    change nm ≤ copyManyCost matrixInputs a + matrixBudget at hnm
    omega
  have hmsize (j : Fin 128) (hj : measuredPort j) : (am.stacks j).length ≤ B + nm :=
    (eval_stack_length_le hem j).trans (Nat.add_le_add_right (hsize j hj) nm)
  have ham123 : am.stacks 123 = List.replicate N true := by
    rw [hmhigh 123 (by decide), hhigh 123 (by decide)]
    simp [N]
  have ham124 : am.stacks 124 = List.replicate (N * N) true := by
    rw [hmhigh 124 (by decide), hhigh 124 (by decide)]
    simp [N]
  have hready : SearchReady p alphabet M am := {
    matrix := hm0
    rows := hm55
    modulus := (hmhigh 108 (by decide)).trans ready.modulus
    zero := (hmhigh 109 (by decide)).trans ready.zero
    alphabet := (hmhigh 116 (by decide)).trans halphabet
    dimension := ham123
    square := ham124
    temporary := (hmhigh 125 (by decide)).trans ready.temporary
    bank := fun i => (hmhigh (searchPorts i) (by simp [searchPorts])).trans (hbank i) }
  obtain ⟨ns, searched, C, d, hns, hes, hgood, hsC, hsd, hsN, hslow, hshigh, hsregs⟩ :=
    runSearch_eval p alphabet hfull M am hready
  have hns' : ns ≤ 186 * (B + nm) + 235 + searchBudget := by
    have hc := searchCost_le p alphabet m N am (B + nm)
      (fun pair hp => hmsize _ (searchInputs_measured pair hp))
      (fun j hj => hmsize j (Or.inl (by omega)))
    exact hns.trans hc
  have hssize (j : Fin 128) (hj : measuredPort j) : (searched.stacks j).length ≤ B + nm + ns :=
    (eval_stack_length_le hes j).trans (Nat.add_le_add_right (hmsize j hj) ns)
  have hshigh' (j : Fin 128) (hj : 107 ≤ j.val) : searched.stacks j =
      Function.update (Function.update base.stacks 123 (List.replicate N true)) 124
        (List.replicate (N * N) true) j :=
    (hshigh j hj).trans ((hmhigh j (by omega)).trans (hhigh j hj))
  have hs125 : searched.stacks 125 = [] :=
    (hshigh 125 (by decide)).trans ((hmhigh 125 (by decide)).trans ready.temporary)
  have hs126 : searched.stacks 126 = [] := by
    simpa [h126] using hshigh' 126 (by decide)
  have hef := finishSearch_eval searched (hslow 0 (by decide)) hs125 hs126
  have hnf : finishSearchCost searched ≤ 200 * (B + nm + ns + 2) :=
    finishSearchCost_le searched (B + nm + ns) hs126
      (by
        intro j hj
        rcases (searchWork_mem j).mp hj with hj | rfl
        · exact hssize j (Or.inl (by omega))
        · exact hssize 124 (Or.inr (by decide)))
      (hssize 123 (Or.inr (by decide))) (hssize 73 (Or.inl (by decide)))
      (hssize 106 (Or.inl (by decide)))
  refine ⟨nm + (ns + finishSearchCost searched), finishedSearch searched, C, d, ?_,
    hem.seq (hes.seq hef), hgood, ?_⟩
  · change nm + (ns + finishSearchCost searched) ≤
      1000000000 * (B + matrixBudget + searchBudget + 1)
    omega
  · exact finishedSearch_frame base searched (List.replicate N true)
      (List.replicate (N * N) true) (List.replicate d.val true)
      (BlockCoefficientProgram.tableBits p C) hbase hslow hshigh' hsd hsC hs126

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
