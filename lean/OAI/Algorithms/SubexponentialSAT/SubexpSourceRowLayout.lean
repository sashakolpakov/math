import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSourceRowContext
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixFrames
import OAI.Algorithms.SubexponentialSAT.SubexpRowArithmeticRelocation
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialAddService
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionPairSpec

namespace OAI.Algorithms

/-! Extensional layout facts for the actual source-row initializer. These
small proofs inspect only changed ports and preserve the surrounding frame. -/

namespace SubexponentialSAT.SubexpSourceRowReady

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpRowPostfixInterpreter (contextStore physicalCfg ports)
open SubexpRowArithmeticRelocation (bank)

abbrev Data := StructuredProgram.State 16 256

def scalarFrame (a : Data) (i : Fin 6) : List Bool :=
  a.stacks ⟨14 + i.val, by omega⟩

noncomputable def context (a : Data) : Fin 252 → List Bool :=
  fun i => (SubexpSourceRowContext.result a).stacks (ports (Fin.natAdd 4 i))

theorem empty_at (a : Data) (i : Fin 256)
    (hi : SubexpSourceRowContext.NeedsClear i)
    (hd : i ≠ 5 ∧ i ≠ 194 ∧ i ≠ 10 ∧ i ≠ 202 ∧ i ≠ 201 ∧ i ≠ 74 ∧ i ≠ 248)
    (h104 : i ≠ 104) (h242 : i ≠ 242) (h243 : i ≠ 243) :
    (SubexpSourceRowContext.result a).stacks i = [] :=
  SubexpSourceRowContext.result_empty a i hi
    (SubexpSourceRowContext.copies_avoid i hd) h104 h242 h243

theorem contextStore_eq_result (a : Data) :
    contextStore (context a) = (SubexpSourceRowContext.result a).stacks := by
  funext i
  obtain ⟨j, rfl⟩ := ports.surjective i
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro j
    fin_cases j
    all_goals
      change [] = _
      symm
      exact empty_at a _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro j
    exact SubexpRowPostfixInterpreter.physicalCfg_context _ _ _ _ _ _ _ _ j

private theorem result_low (a : Data) (i : Fin 20) :
    (SubexpSourceRowContext.result a).stacks (SubexpPolynomialAddService.ports i) =
      if i = 5 then a.stacks 128 else if i = 10 then a.stacks 129
      else if i.val < 14 then [] else a.stacks (SubexpPolynomialAddService.ports i) := by
  by_cases h5 : i = 5
  · subst i
    simpa [SubexpPolynomialAddService.ports] using SubexpSourceRowContext.result_word a (128, 5)
      (by simp [SubexpSourceRowContext.copies]) (by decide)
  by_cases h10 : i = 10
  · subst i
    simpa [SubexpPolynomialAddService.ports] using SubexpSourceRowContext.result_word a (129, 10)
      (by simp [SubexpSourceRowContext.copies]) (by decide)
  have hv5 : i.val ≠ 5 := fun h => h5 (Fin.ext h)
  have hv10 : i.val ≠ 10 := fun h => h10 (Fin.ext h)
  by_cases hi : i.val < 14
  · simp only [h5, h10, hi, ite_false, ite_true]
    have hbound : (SubexpPolynomialAddService.ports i).val < 14 := hi
    have hne (j : Fin 256) (hj : 14 ≤ j.val) : SubexpPolynomialAddService.ports i ≠ j := by
      intro heq
      have hv := congrArg Fin.val heq
      omega
    exact empty_at a _ (Or.inl hi)
      ⟨(fun heq => h5 (Fin.ext (congrArg (fun x : Fin 256 => x.val) heq))), hne 194 (by decide),
        (fun heq => h10 (Fin.ext (congrArg (fun x : Fin 256 => x.val) heq))), hne 202 (by decide),
        hne 201 (by decide), hne 74 (by decide), hne 248 (by decide)⟩
      (hne 104 (by decide)) (hne 242 (by decide)) (hne 243 (by decide))
  · simp only [h5, h10, hi, ite_false]
    apply SubexpSourceRowContext.result_frame
    simp only [SubexpSourceRowContext.NeedsClear, SubexpPolynomialAddService.ports,
      Function.Embedding.coeFn_mk, Fin.ext_iff, Fin.val_castAdd, Fin.coe_ofNat_eq_mod]
    have := i.isLt
    omega

theorem low_layout (a : Data) :
    ∀ i, (SubexpSourceRowContext.result a).stacks (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) (a.stacks 128) [] []
        (a.stacks 129) [] (scalarFrame a)).stacks i := by
  intro i
  rw [result_low]
  fin_cases i <;> simp [DensePolynomialLoop.ready, DensePolynomialLoop.state,
    DensePolynomialLoop.stackArray, SubexpPolynomialAddService.ports,
    scalarFrame, Fin.addCases, Fin.coe_ofNat_eq_mod]

private theorem bank_high_value (i : Fin 77) :
    (bank (SubexpConvolutionPair.highPort i)).val =
      if i.val < 10 then 214 + i.val else 128 + i.val := by
  have hi := i.isLt
  change (SubexpRowArithmeticRelocation.bankIndex
    ⟨128 + i.val, by omega⟩).val = if i.val < 10 then 214 + i.val else 128 + i.val
  by_cases h : i.val < 10
  · have h' : 128 ≤ 128 + i.val ∧ 128 + i.val < 138 := by omega
    simp only [SubexpRowArithmeticRelocation.bankIndex, Fin.val_mk,
      dite_eq_left h', ite_eq_left h]
    omega
  · have h' : ¬ (128 ≤ 128 + i.val ∧ 128 + i.val < 138) := by omega
    have h'' : ¬ (214 ≤ 128 + i.val ∧ 128 + i.val < 224) := by omega
    simp only [SubexpRowArithmeticRelocation.bankIndex, Fin.val_mk,
      dite_eq_right h', dite_eq_right h'', ite_eq_right h]

private theorem high_empty (a : Data) (i : Fin 77)
    (h66 : i ≠ 66) (h73 : i ≠ 73) (h74 : i ≠ 74) :
    (SubexpSourceRowContext.result a).stacks (bank (SubexpConvolutionPair.highPort i)) = [] := by
  have hi := i.isLt
  have hv66 : i.val ≠ 66 := fun h => h66 (Fin.ext h)
  have hv73 : i.val ≠ 73 := fun h => h73 (Fin.ext h)
  have hv74 : i.val ≠ 74 := fun h => h74 (Fin.ext h)
  apply empty_at
  · simp only [SubexpSourceRowContext.NeedsClear, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, bank_high_value]
    split_ifs <;> omega
  · repeat' constructor
    all_goals
      intro heq
      have hv := congrArg Fin.val heq
      rw [bank_high_value] at hv
      norm_num at hv
      split_ifs at hv <;> omega
  all_goals
    intro heq
    have hv := congrArg Fin.val heq
    rw [bank_high_value] at hv
    norm_num at hv
    split_ifs at hv <;> omega

theorem high_layout (a : Data) (i : Fin 77) :
    (SubexpSourceRowContext.result a).stacks (bank (SubexpConvolutionPair.highPort i)) =
      SubexpQuarticFlatMul.bankStore (fun _ => []) (a.stacks 128)
        (a.stacks 130) (a.stacks 129) [] i := by
  by_cases h66 : i = 66
  · subst i
    have hport : bank (SubexpConvolutionPair.highPort (66 : Fin 77)) = 194 := by
      apply Fin.ext
      rw [bank_high_value]
      decide
    rw [hport]
    simpa [SubexpQuarticFlatMul.bankStore] using SubexpSourceRowContext.result_word a (128, 194)
      (by simp [SubexpSourceRowContext.copies]) (by decide)
  by_cases h73 : i = 73
  · subst i
    have hport : bank (SubexpConvolutionPair.highPort (73 : Fin 77)) = 201 := by
      apply Fin.ext
      rw [bank_high_value]
      decide
    rw [hport]
    simpa [SubexpQuarticFlatMul.bankStore] using SubexpSourceRowContext.result_word a (130, 201)
      (by simp [SubexpSourceRowContext.copies]) (by decide)
  by_cases h74 : i = 74
  · subst i
    have hport : bank (SubexpConvolutionPair.highPort (74 : Fin 77)) = 202 := by
      apply Fin.ext
      rw [bank_high_value]
      decide
    rw [hport]
    simpa [SubexpQuarticFlatMul.bankStore] using SubexpSourceRowContext.result_word a (129, 202)
      (by simp [SubexpSourceRowContext.copies]) (by decide)
  rw [high_empty a i h66 h73 h74]
  simp [SubexpQuarticFlatMul.bankStore, h66, h73, h74]

end SubexponentialSAT.SubexpSourceRowReady

end OAI.Algorithms
