import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgramFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgramValue

namespace OAI.Algorithms

/-! Fixed native table-entry selector. The only input magnitudes are unary
stack data. Output registers 5,6,7 encode the six possible small coefficients. -/
namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

abbrev selectJ (a : ℕ) : Cmd 8 4 :=
  .ite 5 (lookup (coefficientsAt (a+1)))
    (.ite 6 (lookup (coefficientsAt (a+2))) (lookup (coefficientsAt a)))

abbrev select : Cmd 8 4 :=
  .ite 3 (selectJ 1) (.ite 4 (selectJ 2) (selectJ 0))

theorem selectJ_eval (a : ℕ) (b : Fin 3) (n : ℕ)
    (r : Fin 8 → Bool) (xs ys bs : List Bool)
    (h5 : r 5 = decide (b.val=1)) (h6 : r 6 = decide (b.val=2)) :
    ∃ steps rf zs, steps ≤ 15 ∧
      Eval (selectJ a) steps (data r xs ys (List.replicate n true) bs)
        (data rf xs ys zs bs) ∧
      (∀ z, rf (outputPort z) =
        codeBits (((coefficientsAt (a+b.val))[n]?).getD 0) z) ∧ zs.length ≤ n := by
  obtain ⟨steps,rf,zs,hc,he,hbits,hz⟩ := lookup_eval (coefficientsAt (a+b.val)) n r xs ys bs
  rw [coefficientsAt_length] at hc
  refine ⟨steps+(if b.val=1 then 1 else 2),rf,zs,by split_ifs <;> omega,?_,hbits,hz⟩
  fin_cases b
  · simpa [selectJ,Nat.add_assoc] using Eval.ite_false (test := 5) (yes := lookup (coefficientsAt (a+1))) h5
      (Eval.ite_false (test := 6) (yes := lookup (coefficientsAt (a+2))) h6 he)
  · simpa [selectJ,Nat.add_assoc] using Eval.ite_true (test := 5)
      (no := .ite 6 (lookup (coefficientsAt (a+2))) (lookup (coefficientsAt a))) h5 he
  · simpa [selectJ,Nat.add_assoc] using Eval.ite_false (test := 5) (yes := lookup (coefficientsAt (a+1))) h5
      (Eval.ite_true (test := 6) (no := lookup (coefficientsAt a)) h6 he)

theorem select_eval (a b : Fin 3) (n : ℕ)
    (r : Fin 8 → Bool) (xs ys bs : List Bool)
    (h3 : r 3 = decide (a.val=1)) (h4 : r 4 = decide (a.val=2))
    (h5 : r 5 = decide (b.val=1)) (h6 : r 6 = decide (b.val=2)) :
    ∃ steps rf zs, steps ≤ 17 ∧
      Eval select steps (data r xs ys (List.replicate n true) bs)
        (data rf xs ys zs bs) ∧
      (∀ z, rf (outputPort z) =
        codeBits (((coefficientsAt (a.val+b.val))[n]?).getD 0) z) ∧ zs.length ≤ n := by
  obtain ⟨steps,rf,zs,hc,he,hbits,hz⟩ := selectJ_eval a.val b n r xs ys bs h5 h6
  refine ⟨steps+(if a.val=1 then 1 else 2),rf,zs,by split_ifs <;> omega,?_,hbits,hz⟩
  fin_cases a
  · simpa [select,Nat.add_assoc] using Eval.ite_false (test := 3) (yes := selectJ 1) h3
      (Eval.ite_false (test := 4) (yes := selectJ 2) h4 he)
  · simpa [select,Nat.add_assoc] using Eval.ite_true (test := 3) (no := .ite 4 (selectJ 2) (selectJ 0)) h3 he
  · simpa [select,Nat.add_assoc] using Eval.ite_false (test := 3) (yes := selectJ 1) h3
      (Eval.ite_true (test := 4) (no := selectJ 0) h4 he)

abbrev finish : Cmd 8 4 := .ite 7 (emit 0) select
abbrev command : Cmd 8 4 := .seq scanI (.seq scanJ (.seq subtract finish))
def program := compiled command 0 2

theorem instruction_count : size command + 1 = 306 := by rfl

theorem command_eval (i j k : ℕ) (r : Fin 8 → Bool) :
    ∃ steps rf zs bs, steps ≤ 8*(i+j)+32 ∧
      Eval command steps
        (data r (List.replicate i true) (List.replicate j true)
          (List.replicate k true) [])
        (data rf [] [] zs bs) ∧
      (∀ z, rf (outputPort z) = codeBits (entryCode i j k) z) ∧
      zs.length + bs.length ≤ i+j+k := by
  let r₁ := afterI r i
  let r₂ := afterJ r₁ j
  let a := 3*(i/3+j/3)
  have hI := scanI_eval i r (List.replicate j true) (List.replicate k true) []
  have hJ := scanJ_eval j r₁ [] (List.replicate k true) (List.replicate (3*(i/3)) true)
  have hsum : List.replicate (3*(j/3)) true ++ List.replicate (3*(i/3)) true =
      List.replicate a true := by
    rw [← List.replicate_add]
    congr 1
    dsimp [a]; omega
  simp only [List.append_nil] at hI
  rw [hsum] at hJ
  obtain ⟨ns,rs,bs,hs,he,hr,hbs⟩ := subtract_eval a k r₂ [] []
  let r₃ := afterSub r₂ rs
  have hf : ∃ nf rf zs, nf ≤ 18 ∧
      Eval finish nf (data r₃ [] [] (List.replicate (k-a) true) bs)
        (data rf [] [] zs bs) ∧
      (∀ z, rf (outputPort z) = codeBits (entryCode i j k) z) ∧
      zs.length ≤ k-a := by
    by_cases hka : k < a
    · have h7 : (data r₃ [] [] (List.replicate (k-a) true) bs).regs 7 = true := by
        simpa [data,r₃,afterSub,hka] using hr
      refine ⟨4,setOutput r₃ 0,List.replicate (k-a) true,by omega,
        Eval.ite_true h7 (emit_eval _ 0),?_,by simp⟩
      intro z; fin_cases z <;> simp [entryCode,show k < 3*(i/3+j/3) from hka,
        outputPort,setOutput]
    · have h7 : (data r₃ [] [] (List.replicate (k-a) true) bs).regs 7 = false := by
        simpa [data,r₃,afterSub,hka] using hr
      obtain ⟨nf,rf,zs,hn,hf,hbits,hz⟩ := select_eval
        ⟨i%3,Nat.mod_lt _ (by decide)⟩ ⟨j%3,Nat.mod_lt _ (by decide)⟩
        (k-a) r₃ [] [] bs rfl rfl rfl rfl
      refine ⟨nf+1,rf,zs,by omega,Eval.ite_false h7 hf,?_,hz⟩
      simpa [entryCode,show ¬ k < 3*(i/3+j/3) from hka,a] using hbits
  obtain ⟨nf,rf,zs,hfc,hfinish,hbits,hzs⟩ := hf
  refine ⟨(10*(i/3)+2*(i%3)+5)+((10*(j/3)+2*(j%3)+5)+(ns+nf)),rf,zs,bs,
    ?_,hI.seq (hJ.seq (he.seq hfinish)),hbits,?_⟩
  · have hi := scan_cost i
    have hj := scan_cost j
    have ha : a ≤ i+j := by dsimp [a]; omega
    omega
  · have ha : a ≤ i+j := by dsimp [a]; omega
    omega

/-- A real fixed instruction-table trace, including its final halt. -/
theorem program_trace (i j k : ℕ) (r : Fin 8 → Bool) :
    ∃ steps rf zs bs, steps ≤ 40*(i+j+k+1) ∧
      Trace program steps
        ((data r (List.replicate i true) (List.replicate j true)
          (List.replicate k true) []).withPC (some program.entry))
        ((data rf [] [] zs bs).withPC none) ∧
      (∀ z, rf (outputPort z) = codeBits (entryCode i j k) z) ∧
      zs.length + bs.length ≤ i+j+k := by
  obtain ⟨steps,rf,zs,bs,hc,he,hbits,hz⟩ := command_eval i j k r
  exact ⟨steps+1,rf,zs,bs,by omega,compiled_halt_trace he 0 2,hbits,hz⟩

/-- Correct small coefficient, with no integer-arithmetic callback. -/
theorem program_hadicTable {t : ℕ} (i j k : Fin (3*t)) (r : Fin 8 → Bool) :
    ∃ steps rf zs bs, ∃ c : Fin 6, steps ≤ 40*(i.val+j.val+k.val+1) ∧
      Trace program steps
        ((data r (List.replicate i.val true) (List.replicate j.val true)
          (List.replicate k.val true) []).withPC (some program.entry))
        ((data rf [] [] zs bs).withPC none) ∧
      (∀ z, rf (outputPort z) = codeBits c z) ∧
      codeValue c = IdempotentProgram.hadicTable i j k ∧
      zs.length + bs.length ≤ i.val+j.val+k.val := by
  obtain ⟨steps,rf,zs,bs,hc,he,hbits,hz⟩ := program_trace i.val j.val k.val r
  exact ⟨steps,rf,zs,bs,entryCode i.val j.val k.val,hc,he,hbits,entryCode_correct i j k,hz⟩

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
