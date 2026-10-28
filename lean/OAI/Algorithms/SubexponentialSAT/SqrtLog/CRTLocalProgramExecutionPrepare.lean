import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramExecutionInit
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramInverseConstants

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

/-- Definitionally identical to the final controller's preparation code. -/
def executionPreparation (sm sa : Code) : Code :=
  .seq (SubexpLocalCRTSetup.clearMany [217,229])
    (.seq (replace 240 223) (.seq (clear 240) (.seq constantCommand
      (.seq (inverseConstantsCommand sm sa)
        (.seq (SubexpPolynomialConstructor.construct 207 104 220) (copy 192 242))))))

theorem lowFrame_clearMany {base s : Store} (hf : LowFrame base s)
    (slots : List (Fin 256)) (hs : ∀ i ∈ slots, 205 ≤ i.val) :
    LowFrame base (SubexpLocalCRTSetup.cleared slots s) := by
  intro i hi
  have hnot : i ∉ slots := by intro h; have := hs i h; omega
  simpa [SubexpLocalCRTSetup.cleared_apply, hnot] using hf i hi

def preparationBudget (e t J Km Ka W V U : ℕ) : ℕ :=
  2 * (2 * U + 3) + (9 * V + 8) + (2 * V + 3) + (21 * W + 9 * V + 19) +
    inverseConstantsBudget e t J Km Ka W + 220 * (J + 1) * (W + 1) + (7 * V + 5)

def preparedLocal (s : Store) (factor one inverse negInverse zero : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update s 240 []) 223 factor) 227 inverse) 228 negInverse) 220 one) 242 zero

theorem prepareLocalInverse_run {C P : Type*} (base : Store)
    (encC : C → List Bool) (encP : P → List Bool) (constant : C → P)
    (sm sa : Code) (cm ca : C → C → C) (Km Ka W V J U : ℕ)
    (hsm : ServiceSpec base encC sm cm Km) (hsa : ServiceSpec base encC sa ca Ka)
    (hcwidth : ∀ c, (encC c).length = W) (hpwidth : ∀ p, (encP p).length ≤ V)
    (zero one minusOne c : C) (factor : P) (rest : List Bool)
    (hconstant : ∀ a, encP (constant a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC zero) J)
    (hhead : encP factor = encC c ++ rest)
    (s : Store) (hf : LowFrame base s)
    (hfactor : s 240 = encP factor) (hzero : s 104 = encC zero)
    (hzeroBits : encC zero = List.replicate W false)
    (hone : s 207 = encC one) (hminus : s 211 = encC minusOne)
    (hJ : s 243 = List.replicate J true) (hpolyZero : s 192 = encP (constant zero))
    (hcursor : ∀ i ∈ ([217,229] : List (Fin 256)), (s i).length ≤ U)
    (hclean : ∀ i ∈ ([100,101,102,107,108,120,121,122,205,208,220,222,223,
        227,228,241,242,244,245,246,247] : List (Fin 256)), s i = []) :
    let a := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
    ExecutesIn (executionPreparation sm sa)
      (preparationBudget (s 209).length (s 212).length J Km Ka W V U) s
      (preparedLocal (SubexpLocalCRTSetup.cleared [217,229] s)
        (encP factor) (encP (constant one)) (encP (constant a))
        (encP (constant (cm a minusOne))) (encP (constant zero))) := by
  dsimp only
  let a := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
  let t0 := SubexpLocalCRTSetup.cleared [217,229] s
  let t1 := Function.update t0 223 (encP factor)
  let t2 := Function.update t1 240 []
  let t3 := Function.update t2 205 (encC c)
  let t4 := Function.update (Function.update t2 227 (encP (constant a))) 228
    (encP (constant (cm a minusOne)))
  let t5 := Function.update t4 220 (encP (constant one))
  let t6 := Function.update t5 242 (encP (constant zero))
  have hf0 : LowFrame base t0 := lowFrame_clearMany hf _ (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> decide)
  have hf3 : LowFrame base t3 := lowFrame_update (lowFrame_update
    (lowFrame_update hf0 223 (by decide) _) 240 (by decide) _) 205 (by decide) _
  have hrest : rest.length ≤ V := by
    have hh := hpwidth factor
    rw [hhead, List.length_append, hcwidth] at hh
    omega
  have h0 : ExecutesIn (SubexpLocalCRTSetup.clearMany [217,229]) (2 * (2 * U + 3)) s t0 := by
    simpa [t0] using SubexpLocalCRTSetup.clearMany_run [217,229] s U hcursor
  have h1 : ExecutesIn (replace 240 223) (9 * V + 8) t0 t1 := by
    have h := replace_bounded t0 240 223 V (by decide) (by decide) (by decide)
      (by simp [t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simpa [t0, SubexpLocalCRTSetup.cleared_apply, hfactor] using hpwidth factor)
      (by simp [t0, SubexpLocalCRTSetup.cleared_apply, hclean])
    simpa [t1, t0, SubexpLocalCRTSetup.cleared_apply, hfactor] using h
  have h2 : ExecutesIn (clear 240) (2 * V + 3) t1 t2 := by
    apply (clear_run 240 t1).mono
    have hh := hpwidth factor
    simpa [t1, t0, SubexpLocalCRTSetup.cleared_apply, hfactor] using
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 hh) 3
  have h3 : ExecutesIn constantCommand (21 * W + 9 * V + 19) t2 t3 := by
    have h := constantCommand_run t2 (encC c) rest
      (by simp [t2, t1, hhead])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hzero, hcwidth])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
    apply h.mono
    rw [hcwidth]
    omega
  have h4 : ExecutesIn (inverseConstantsCommand sm sa)
      (inverseConstantsBudget (s 209).length (s 212).length J Km Ka W) t3 t4 := by
    have h := inverseConstantsCommand_run base encC sm sa cm ca Km Ka W J hsm hsa hcwidth
      t3 c zero one minusOne hf3 (by simp [t3])
      (by simp [t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hzero]) hzeroBits
      (by simp [t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hone])
      (by simp [t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hminus])
      (by simp [t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hJ])
      (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          <;> simp [t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
    have he : Function.update t2 205 [] = t2 := by
      apply Function.update_eq_self_iff.mpr
      simp [t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean]
    simp only [t3, Function.update_idem, he] at h
    simpa [t4, t3, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, a,
      ← hconstant, hclean, Function.update_idem] using h
  have h5 : ExecutesIn (SubexpPolynomialConstructor.construct 207 104 220)
      (220 * (J + 1) * (W + 1)) t4 t5 := by
    have h := DensePolynomialProgram.Constructor.construct_run t4 207 104 220
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      J W
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hone, hcwidth])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hzero, hcwidth])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hJ])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hzero, hzeroBits])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
      (by simp [t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
    simpa [t5, t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hone, hzero, hconstant] using h
  have h6 : ExecutesIn (copy 192 242) (7 * V + 5) t5 t6 := by
    have h := copy_run 192 242 t5 (by decide) (by decide) (by decide)
      (by simp [t5, t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hclean])
    have hh : (t5 192).length ≤ V := by
      simpa [t5, t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hpolyZero] using hpwidth (constant zero)
    have h' := h.mono (show 7 * (t5 192).length + 5 ≤ 7 * V + 5 by omega)
    simpa [t6, t5, t4, t2, t1, t0, SubexpLocalCRTSetup.cleared_apply, hpolyZero, hclean] using h'
  have he : t6 = preparedLocal t0 (encP factor) (encP (constant one))
      (encP (constant a)) (encP (constant (cm a minusOne))) (encP (constant zero)) := by
    simp only [t6, t5, t4, t2, t1, preparedLocal]
    rw [Function.update_comm (by decide : (223 : Fin 256) ≠ 240)]
  change ExecutesIn (executionPreparation sm sa)
    (preparationBudget (s 209).length (s 212).length J Km Ka W V U) s
    (preparedLocal t0 (encP factor) (encP (constant one)) (encP (constant a))
      (encP (constant (cm a minusOne))) (encP (constant zero)))
  rw [← he]
  convert h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))) using 1 <;>
    simp only [executionPreparation, preparationBudget] ; ring

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
