import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchColorCore
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchPrepared
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchLoop
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryBudgetBounds

namespace OAI.Algorithms

/-! The actual color callback, with its matrix-entry cost discharged. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls

def entryExtent (p r Q Δ R : ℕ) : ℕ := r + Q + Δ + R + MatrixWordEncoding.width p
def entryCap (p r Q Δ R : ℕ) : ℕ := 500000 * (entryExtent p r Q Δ R + 1)^4

theorem entryCap_bounds (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ} (i : Fin Δ) (t : Fin Q)
    (u y : MulticolorTypes.UniversalType r Q Δ) (coefficients : List (ZMod p)) :
    ConstraintEntryProgram.programBudget p i t u y coefficients ≤ entryCap p r Q Δ coefficients.length := by
  apply MatrixEntryBudgetBounds.constraint_programBudget_le p i t u y coefficients
    (entryExtent p r Q Δ coefficients.length) <;> unfold entryExtent <;> omega

noncomputable def GoodResult (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (coefficients : List (ZMod p))
    (t g : ℕ) (payload : Word) : Prop :=
  ∃ (ht : t < Q) (hg : g < r)
    (C : Fin (TypeEnumeration.sideList (Δ := Δ) hr hQ ⟨t, ht⟩ ⟨g, hg⟩).length →
      Fin (TypeEnumeration.sideList (Δ := Δ) hr hQ ⟨t, ht⟩ ⟨g, hg⟩).length → ZMod p)
    (d : Fin ((TypeEnumeration.sideList (Δ := Δ) hr hQ ⟨t, ht⟩ ⟨g, hg⟩).length + 1)),
    BlockSearch.GoodPair
      (ConstraintMatrixProgram.matrix (Δ := Δ) p hr hQ ⟨t, ht⟩ ⟨g, hg⟩ coefficients)
      (BlockSearchEncoding.splitPair d C) ∧
    payload = resultPayload
      (List.replicate (TypeEnumeration.sideList (Δ := Δ) hr hQ ⟨t, ht⟩ ⟨g, hg⟩).length true)
      (List.replicate d.val true) (BlockCoefficientProgram.tableBits p C)

noncomputable def colorPointBudget (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (coefficients alphabet : List (ZMod p))
    (t : Fin Q) (g : Fin r) : ℕ :=
  sideDimensionsCost r Q Δ t.val g.val +
    colorTailBudget (Δ := Δ) p hr hQ t g coefficients alphabet
      (entryCap p r Q Δ coefficients.length)
      (colorExtent p r Q Δ coefficients alphabet t.val g.val)

noncomputable def colorBudget (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (coefficients alphabet : List (ZMod p)) : ℕ :=
  Finset.univ.sup fun t : Fin Q => Finset.univ.sup fun g : Fin r =>
    colorPointBudget (Δ := Δ) p hr hQ coefficients alphabet t g

theorem colorPointBudget_le (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (hr : 0 < r) (hQ : 0 < Q) (coefficients alphabet : List (ZMod p))
    (t : Fin Q) (g : Fin r) :
    colorPointBudget (Δ := Δ) p hr hQ coefficients alphabet t g ≤
      colorBudget (Δ := Δ) p hr hQ coefficients alphabet := by
  unfold colorBudget
  exact (Finset.le_sup (f := fun g : Fin r => colorPointBudget (Δ := Δ) p hr hQ coefficients alphabet t g)
    (Finset.mem_univ g)).trans
    (Finset.le_sup (f := fun t : Fin Q => Finset.univ.sup fun g : Fin r =>
      colorPointBudget (Δ := Δ) p hr hQ coefficients alphabet t g) (Finset.mem_univ t))

theorem colorBody_eval (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (h2 : (2 : ZMod p) ≠ 0) (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet)
    (t : Fin Q) (g : Fin r) (oa ia ofuel ifuel : Word) (regs : Fin 32 → Bool) :
    ∃ steps payload finalRegs,
      steps ≤ colorPointBudget (Δ := Δ) p hr hQ coefficients alphabet t g ∧
      GoodResult (Δ := Δ) p hr hQ coefficients t.val g.val payload ∧
      Eval colorBody steps
        (boundaryState (canonicalContext p r Q Δ coefficients alphabet)
          (TypeIndexProgram.unary (Q * r)) t.val g.val oa ia ofuel ifuel regs)
        (boundaryState (canonicalContext p r Q Δ coefficients alphabet)
          (TypeIndexProgram.unary (Q * r)) t.val (g.val + 1) oa
          ((true :: Encoding.frame payload).reverse ++ ia) ofuel ifuel finalRegs) := by
  let ctx := canonicalContext p r Q Δ coefficients alphabet
  let width := TypeIndexProgram.unary (Q * r)
  let base := boundaryState ctx width t.val g.val oa ia ofuel ifuel regs
  let N := (TypeEnumeration.sideList (Δ := Δ) hr hQ t g).length
  obtain ⟨np, a, hnp, hep, hstacks, hsize, hregs⟩ :=
    prepareColor_eval p r Q Δ coefficients alphabet t.val g.val t.isLt g.isLt
      oa ia ofuel ifuel regs
  have load (j : Fin 128) (h53 : j ≠ 53) (h123 : j ≠ 123) (h124 : j ≠ 124) :
      a.stacks j = base.stacks j := by
    rw [hstacks]
    exact preparedColorStacks_frame r Q Δ t.val g.val base j h53 h123 h124
  have ready : MatrixReady p r Q Δ t.val g.val coefficients
      (TypeEnumeration.sideBytes r Q Δ t.val g.val) a := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try { rw [load _ (by decide) (by decide) (by decide)]; rfl }
    · rw [hstacks]
      exact preparedColorStacks_side r Q Δ t.val g.val base
    · intro j hj h53
      have hn (k : Fin 128) (hk : 65 ≤ k.val) : j ≠ k := by
        intro he
        have hv := congrArg Fin.val he
        omega
      rw [load j h53 (hn 123 (by decide)) (hn 124 (by decide))]
      exact boundary_low_empty ctx width t.val g.val oa ia ofuel ifuel regs j (by omega)
  have halphabet : a.stacks 116 = ProgramEncoding.encodeRecords
      (alphabet.map (BlockSearchPredicate.scalarCode p).block) := by
    rw [load 116 (by decide) (by decide) (by decide)]
    rfl
  have hbank (i : Fin 42) : a.stacks (searchPorts i) = [] := by
    have h53 : searchPorts i ≠ 53 := by
      intro he
      have hv := congrArg Fin.val he
      change 65 + i.val = 53 at hv
      omega
    have h123 : searchPorts i ≠ 123 := by
      intro he
      have hv := congrArg Fin.val he
      change 65 + i.val = 123 at hv
      omega
    have h124 : searchPorts i ≠ 124 := by
      intro he
      have hv := congrArg Fin.val he
      change 65 + i.val = 124 at hv
      omega
    rw [load _ h53 h123 h124]
    apply boundary_low_empty
    simp only [searchPorts, Fin.val_mk]
    omega
  have hbase (j : Fin 128) (hj : j.val < 107 ∨ j = 123 ∨ j = 124) : base.stacks j = [] := by
    rcases hj with hj | rfl | rfl
    · exact boundary_low_empty ctx width t.val g.val oa ia ofuel ifuel regs j hj
    · rfl
    · rfl
  have hhigh (j : Fin 128) (hj : 107 ≤ j.val) : a.stacks j =
      Function.update (Function.update base.stacks 123 (List.replicate N true)) 124
        (List.replicate (N * N) true) j := by
    have h53 : j ≠ 53 := by
      intro he
      have hv := congrArg Fin.val he
      change j.val = 53 at hv
      omega
    rw [hstacks]
    simp only [preparedColorStacks, ConstraintMatrixProgram.sideBytes_length hr hQ t g,
      TypeIndexProgram.unary, Function.update_apply, h53, ite_false, N]
    rfl
  obtain ⟨nt, b, C, d, hnt, het, hgood, hb⟩ := colorTail_eval p h2 hr hQ t g
    coefficients alphabet hfull (entryCap p r Q Δ coefficients.length)
    (colorExtent p r Q Δ coefficients alphabet t.val g.val)
    (fun i u _ y _ => entryCap_bounds p i t u y coefficients)
    base a ready halphabet hbank hbase (by rfl) hhigh hsize
  let payload := resultPayload (List.replicate N true) (List.replicate d.val true)
    (BlockCoefficientProgram.tableBits p C)
  have hb' : b = boundaryState ctx width t.val (g.val + 1) oa
      ((true :: Encoding.frame payload).reverse ++ ia) ofuel ifuel b.regs := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · rw [hb]
      funext j
      by_cases h118 : j = 118
      · subst j
        simp [base, boundaryState, List.replicate_succ]
      · by_cases h122 : j = 122
        · subst j
          simp [base, boundaryState, payload, N]
        · simp [base, boundaryState, h118, h122]
          rfl
  refine ⟨np + nt, payload, b.regs, Nat.add_le_add hnp hnt,
    ⟨t.isLt, g.isLt, C, d, hgood, rfl⟩, ?_⟩
  rw [← hb']
  cases hep with
  | seq hs hd =>
      simpa only [colorBody, colorTail, Nat.add_assoc] using hs.seq (hd.seq het)

theorem actualColorStep (p : ℕ) [Fact p.Prime] {r Q Δ : ℕ}
    (h2 : (2 : ZMod p) ≠ 0) (hr : 0 < r) (hQ : 0 < Q)
    (coefficients alphabet : List (ZMod p)) (hfull : ∀ x, x ∈ alphabet) :
    ColorStep colorBody (canonicalContext p r Q Δ coefficients alphabet)
      (TypeIndexProgram.unary (Q * r)) r Q (GoodResult (Δ := Δ) p hr hQ coefficients)
      (colorBudget (Δ := Δ) p hr hQ coefficients alphabet) := by
  intro t ht g hg oa ia ofuel ifuel regs
  obtain ⟨n, payload, finalRegs, hn, hg, he⟩ := colorBody_eval p h2 hr hQ coefficients alphabet hfull
    ⟨t, ht⟩ ⟨g, hg⟩ oa ia ofuel ifuel regs
  exact ⟨n, payload, finalRegs, hn.trans (colorPointBudget_le p hr hQ coefficients alphabet _ _), hg, he⟩

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
