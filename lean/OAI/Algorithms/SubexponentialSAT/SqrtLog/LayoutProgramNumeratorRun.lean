import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramNumeratorScalar

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
open MatrixScanProgram MatrixEntryEvaluation MatrixEntryKernel MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

def value (A R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1) : ℤ :=
  if anchorValid (0 : Fin 1) t u y then
    LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u y else 0

def budget (A R W P : ℕ) (t : Fin Q) (u y : UniversalType r Q 1) : ℕ :=
  guardStageCost r Q 1 0 t.val + MatrixEntryProgram.scanStageCost r Q 1 0 + 3*Q +
  LayoutProgramScalar.FromCounts.totalCost A R (unchangedCount (rows 0 u y)-1)
    (transposedCount (rows 0 u y)) W P +
  2*unchangedCount (rows 0 u y)+2*transposedCount (rows 0 u y)+20

theorem state_counted (c : Saved) (regs : Fin 10 → Bool) (t : Fin Q)
    (u y : UniversalType r Q 1) (uc hc : List Bool) :
    Function.update (Function.update (state c regs t u y [] [] ([],[])).stacks 2 uc) 3 hc =
      (state c regs t u y uc hc ([],[])).stacks := by
  funext j
  by_cases h2 : j=2 <;> by_cases h3 : j=3 <;> by_cases h50 : j=50 <;>
    by_cases h51 : j=51 <;> simp_all [state,Function.update_apply]

/-- The fixed program computes the literal guarded integer numerator and
returns all type words and reusable caches intact. -/
theorem command_eval (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (regs : Fin 10 → Bool) (a : List Bool) (R : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H a.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : a.length ≤ Q) (hQ : 1 ≤ Q) :
    let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R a
    ∃ n ≤ budget a.length R width.length (pairLength power) t u y,
      ∃ rf result, Eval command n (state c regs t u y [] [] ([],[]))
        (state c rf t u y [] [] result) ∧
      pairValue result=value a.length R t u y ∧
      LayoutProgramScalar.wordTotal result ≤ (8*Q)^(2*R) ∧
      pairLength result ≤ (R-(unchangedCount (rows 0 u y)-1))*
        LayoutProgramScalar.termGrowth (2*width.length+pairLength power) := by
  intro c
  obtain ⟨ng,hng,m,hg,hms,hflag⟩ := UniversalEntry.guard_eval t u y
    (state c regs t u y [] [] ([],[])) (guard_project c regs t u y)
  have hm : m = state c m.regs t u y [] [] ([],[]) :=
    congrArg₂ StructuredProgram.State.mk rfl hms
  rw [hm] at hg
  by_cases ha : anchorValid (0 : Fin 1) t u y
  · have h9 : (state c m.regs t u y [] [] ([],[])).regs 9=true := by
      simpa [state,ha] using hflag
    obtain ⟨ns,hns,z,hs,hzs,hcomp⟩ := ScanRestore.command_eval u y
      (state c m.regs t u y [] [] ([],[])) (scan_project c m.regs t u y)
    have hz : z = state c z.regs t u y
        (List.replicate (unchangedCount (rows 0 u y)) true)
        (List.replicate (transposedCount (rows 0 u y)) true) ([],[]) := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      exact hzs.trans (state_counted c m.regs t u y _ _)
    rw [hz] at hs
    by_cases hc : AllCompatible (0 : Fin 1) u y
    · have h7 : (state c z.regs t u y
          (List.replicate (unchangedCount (rows 0 u y)) true)
          (List.replicate (transposedCount (rows 0 u y)) true) ([],[])).regs 7=true := by
        simpa [state,hc] using hcomp
      obtain ⟨hu,huQ,hhQ⟩ := LayoutTriplePreparationProgram.scanCounts_bounds_of_anchor t u y ha hc
      have hu' : unchangedCount (rows 0 u y)-1+1=unchangedCount (rows 0 u y) := by omega
      obtain ⟨nc,hnc,rf,result,he,hv,hmass,hlength⟩ := scalar_eval Hwords width power z.regs a R
        (unchangedCount (rows 0 u y)-1) t u y
        (List.replicate (transposedCount (rows 0 u y)) true)
        hlen hwords hvalues hp hpt (by simpa using (by omega : transposedCount (rows 0 u y)+1 ≤ width.length))
        hAQ hQ (by simpa using hhQ)
      simp only [hu',List.length_replicate] at he hv hnc
      have ht := hg.seq (Eval.ite_true (no := .base .skip) h9
        (hs.seq (Eval.ite_true (no := clearCounts) h7 he)))
      refine ⟨ng+(ns+(nc+1)+1),?_,rf,result,ht,?_,hmass,hlength⟩
      · unfold budget
        omega
      · have hformula := LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry
          a.length R t u y ha
        simpa [value,ha,hc] using hv.trans (by simpa [hc] using hformula)
    · have h7 : (state c z.regs t u y
          (List.replicate (unchangedCount (rows 0 u y)) true)
          (List.replicate (transposedCount (rows 0 u y)) true) ([],[])).regs 7=false := by
        simpa [state,hc] using hcomp
      obtain ⟨rf,he⟩ := clearCounts_eval c z.regs t u y
        (List.replicate (unchangedCount (rows 0 u y)) true)
        (List.replicate (transposedCount (rows 0 u y)) true)
      simp only [List.length_replicate] at he
      have ht := hg.seq (Eval.ite_true (no := .base .skip) h9
        (hs.seq (Eval.ite_false (yes := scalar) h7 he)))
      refine ⟨ng+(ns+(2*unchangedCount (rows 0 u y)+2*transposedCount (rows 0 u y)+6+1)+1),
        ?_,rf,([],[]),ht,?_,?_,?_⟩
      · unfold budget
        omega
      · have hformula := LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry
          a.length R t u y ha
        simpa [value, ha, hc, pairValue, RowSelectionProgram.signedValue] using hformula
      · simp [LayoutProgramScalar.wordTotal,pairTotal]
      · simp [pairLength]
  · have h9 : (state c m.regs t u y [] [] ([],[])).regs 9=false := by
      simpa [state,ha] using hflag
    have ht := hg.seq (Eval.ite_false (yes := guarded) h9
      (Eval.base (StructuredProgram.Eval.skip _)))
    refine ⟨ng+1,?_,m.regs,([],[]),ht,?_,?_,?_⟩
    · unfold budget
      omega
    · simp [value,ha,pairValue,RowSelectionProgram.signedValue,BinaryArithmetic.toNat]
    · simp [LayoutProgramScalar.wordTotal,pairTotal]
    · simp [pairLength]

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
