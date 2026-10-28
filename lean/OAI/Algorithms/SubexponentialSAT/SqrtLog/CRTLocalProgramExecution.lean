import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramExecutionPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram

namespace OAI.Algorithms

/-! Composition of the native local CRT scan, scalar inversion, and
polynomial correction. Service hypotheses refer to fixed finite commands;
they are instantiated by the concrete scalar and array service modules. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem executionInitialization_eq : executionInitialization = initializeLocal := rfl

theorem executionPreparation_eq (sm sa : Code) :
    executionPreparation sm sa = prepareLocalInverse sm sa := rfl

def localBudget (nodes index exponent precision J Km Ka Kp Kap W V : ℕ) : ℕ :=
  initializationBudget J W (nodes * W) index +
  (nodes * (includeBudget Km Ka Kp W V J + 18 * W + 28) + 2) +
  preparationBudget exponent precision J Km Ka W V (index + 1) +
  correctionBudget J Kp Kap V + 5 * (2 * V + 3) + 2

def localWork : List (Fin 256) :=
  [100,101,102,107,108,120,121,122,205,208,215,217,218,219,220,222,223,
   224,227,228,229,240,241,242,244,245,246,247]

theorem localClean_subset {s : Store} (hclean : ∀ i ∈ localWork, s i = [])
    (slots : List (Fin 256)) (hsub : slots ⊆ localWork) : ∀ i ∈ slots, s i = [] :=
  fun i hi => hclean i (hsub hi)

theorem positiveLocal_run {C P : Type*} (s : Store)
    (encC : C → List Bool) (encP : P → List Bool)
    (constant linear : C → P) (sm sa pm pa : Code)
    (cm ca : C → C → C) (mulP addP : P → P → P)
    (Km Ka Kp Kap W V J : ℕ) (hW : 0 < W)
    (hsm : ServiceSpec s encC sm cm Km) (hsa : ServiceSpec s encC sa ca Ka)
    (hpm : ServiceSpec s encP pm mulP Kp) (hpa : ServiceSpec s encP pa addP Kap)
    (hcwidth : ∀ c, (encC c).length = W) (hpwidth : ∀ p, (encP p).length ≤ V)
    (zero one minusOne theta c : C) (cs : List C) (jet : P) (rest : List Bool)
    (hconstant : ∀ a, encP (constant a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC zero) J)
    (hlinear : ∀ a, encP (linear a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC one) J)
    (hzero : s 104 = encC zero) (hzeroBits : encC zero = List.replicate W false)
    (hone : s 207 = encC one) (hminus : s 211 = encC minusOne)
    (htheta : s 213 = encC theta) (hcs : s 214 = cs.flatMap encC)
    (hJ : s 243 = List.replicate J true) (hjet : s 225 = encP jet)
    (hpolyZero : s 192 = encP (constant zero))
    (hclean : ∀ i ∈ localWork, s i = [])
    (hhead : encP ((cs.eraseIdx (s 216).length).foldl
      (localUpdate cm ca mulP linear theta minusOne J) (constant one)) = encC c ++ rest) :
    let factor := (cs.eraseIdx (s 216).length).foldl
      (localUpdate cm ca mulP linear theta minusOne J) (constant one)
    let inv := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
    ExecutesIn (positiveLocal sm sa pm pa)
      (localBudget cs.length (s 216).length (s 209).length (s 212).length J Km Ka Kp Kap W V - 2)
      s (Function.update s 244 (encP (correctionValue mulP addP (constant zero) (constant one)
        (constant (cm inv minusOne)) (constant inv) factor jet J))) := by
  dsimp only
  let update := localUpdate cm ca mulP linear theta minusOne J
  let factor := (cs.eraseIdx (s 216).length).foldl update (constant one)
  let inv := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
  let x := SubexpNodeScanControl.run update cs ⟨constant one, s 216, true⟩
  let start := SubexpNodeScanControl.ready s encC encP cs ⟨constant one, s 216, true⟩ [] []
  let scanned := SubexpNodeScanControl.ready s encC encP [] x [] []
  let prepared := preparedLocal s (encP factor) (encP (constant one))
    (encP (constant inv)) (encP (constant (cm inv minusOne))) (encP (constant zero))
  let value := correctionValue mulP addP (constant zero) (constant one)
    (constant (cm inv minusOne)) (constant inv) factor jet J
  let corrected := Function.update prepared 244 (encP value)
  have hx : x.value = factor := SubexpNodeScanControl.run_skip_index update cs (s 216) (constant one)
  have hinit : ExecutesIn initializeLocal
      (initializationBudget J W (cs.length * W) (s 216).length) s start := by
    have h := initializeLocal_run s J W hJ (by simp [hone, hcwidth])
      (hzero.trans hzeroBits) (localClean_subset hclean _ (by decide))
    have hlen : (s 214).length = cs.length * W := by
      rw [hcs, List.length_flatMap]
      simp [hcwidth]
    rw [hlen] at h
    have hb : DensePolynomialProgram.Constructor.Counter.paddedBits W (s 207) (s 104) J =
        encP (constant one) := by simp [hone, hzero, hconstant]
    rw [hb, initializedLocal_eq_ready s encC encP cs (constant one) hcs
      (hclean 218 (by simp [localWork])) (hclean 219 (by simp [localWork]))] at h
    exact h
  have hinclude := includeNode_spec s encC encP sm sa pm cm ca mulP Km Ka Kp W V J
    theta one minusOne linear hsm hsa hpm hcwidth hpwidth hlinear htheta hone hminus hJ
    (hzero.trans hzeroBits) (localClean_subset hclean _ (by decide))
  have hscan : ExecutesIn (scanCommand sm sa pm)
      (cs.length * (includeBudget Km Ka Kp W V J + 18 * W + 28) + 2) start scanned :=
    SubexpNodeScanControl.command_run (includeNodeCommand sm sa pm) s encC encP
      (fun _ => []) update (includeBudget Km Ka Kp W V J) W hinclude hcwidth hW
      (by intro c; simp) (by simp [hzero, hcwidth])
      (hclean 121 (by simp [localWork])) (hclean 122 (by simp [localWork])) cs
      ⟨constant one, s 216, true⟩
  have scanframe (i : Fin 256) (hi : ¬ ∃ j, SubexpNodeScanControl.ports j = i) :
      scanned i = s i := SubexpNodeScanControl.work_frame s _ i hi
  have hprep : ExecutesIn (prepareLocalInverse sm sa)
      (preparationBudget (s 209).length (s 212).length J Km Ka W V ((s 216).length + 1)) scanned prepared := by
    have h := prepareLocalInverse_run s encC encP constant sm sa cm ca Km Ka W V J
      ((s 216).length + 1) hsm hsa hcwidth hpwidth zero one minusOne c factor rest hconstant hhead
      scanned (scanReady_low s encC encP [] x [] [])
      (by simp [scanned, SubexpNodeScanControl.ready, SubexpNodeScanControl.words, hx])
      ((scanframe 104 (by decide)).trans hzero) hzeroBits
      ((scanframe 207 (by decide)).trans hone) ((scanframe 211 (by decide)).trans hminus)
      ((scanframe 243 (by decide)).trans hJ) ((scanframe 192 (by decide)).trans hpolyZero)
      (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · have hh := scan_skip_length_le update cs (⟨constant one, s 216, true⟩ : SubexpNodeScanControl.Cursor P)
          simpa [scanned, SubexpNodeScanControl.ready, SubexpNodeScanControl.words] using
            hh.trans (Nat.le_succ _)
        · cases hp : x.pending <;>
            simp [scanned, SubexpNodeScanControl.ready, SubexpNodeScanControl.words,
              SubexpNodeScanControl.marker, hp])
      (by
        intro i hi
        have hiport : ¬ ∃ j, SubexpNodeScanControl.ports j = i := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        have hsub : ([100,101,102,107,108,120,121,122,205,208,220,222,223,
          227,228,241,242,244,245,246,247] : List (Fin 256)) ⊆ localWork := by decide
        exact (scanframe i hiport).trans (hclean i (hsub hi)))
    have hclear : SubexpLocalCRTSetup.cleared [217,229] scanned =
        Function.update s 240 (encP factor) := by
      simpa only [scanned, hx] using cleared_scan_eq_factor s encC encP x
        (localClean_subset hclean _ (by decide))
    have h240 : Function.update s 240 [] = s := by
      apply Function.update_eq_self_iff.mpr
      exact (hclean 240 (by simp [localWork])).symm
    rw [← executionPreparation_eq]
    simpa only [scanframe 209 (by decide), scanframe 212 (by decide),
      hclear, prepared, inv, preparedLocal, Function.update_idem, h240] using h
  have hpreparedLow : LowFrame s prepared := by
    unfold prepared preparedLocal
    repeat' apply lowFrame_update _ _ (by decide) _
    exact lowFrame_refl s
  have hc : ExecutesIn (correctionCommand pm pa) (correctionBudget J Kp Kap V)
      prepared corrected := by
    have h := correctionCommand_run s encP pm pa mulP addP Kp Kap V hpm hpa hpwidth
      prepared (constant zero) (constant one) (constant (cm inv minusOne)) (constant inv)
      factor jet hpreparedLow
      (by simp [prepared, preparedLocal]) (by simp [prepared, preparedLocal])
      (by simp [prepared, preparedLocal]) (by simp [prepared, preparedLocal])
      (by simp [prepared, preparedLocal]) (by simp [prepared, preparedLocal, hjet])
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal])
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
      (by simp [prepared, preparedLocal] ; exact hclean _ (by decide))
    simpa [corrected, value, prepared, preparedLocal, hJ] using h
  have hcleanup : ExecutesIn (SubexpLocalCRTSetup.clearMany [220,223,227,228,242])
      (5 * (2 * V + 3)) corrected (Function.update s 244 (encP value)) := by
    have h := SubexpLocalCRTSetup.clearMany_run [220,223,227,228,242] corrected V (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        simpa [corrected, prepared, preparedLocal] using hpwidth _)
    have he : SubexpLocalCRTSetup.cleared [220,223,227,228,242] corrected =
        Function.update s 244 (encP value) := by
      funext i
      by_cases hi : i ∈ ([220,223,227,228,242] : List (Fin 256))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;>
          simp [SubexpLocalCRTSetup.cleared_apply] <;>
          exact hclean _ (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        rcases hi with ⟨h220,h223,h227,h228,h242⟩
        by_cases h240 : i = 240
        · subst i
          simp [SubexpLocalCRTSetup.cleared_apply, corrected, prepared, preparedLocal] ;
            exact hclean _ (by decide)
        · simp [SubexpLocalCRTSetup.cleared_apply, corrected, prepared, preparedLocal,
            Function.update_apply, h220,h223,h227,h228,h242,h240]
    simpa only [he, List.length_cons, List.length_nil] using h
  apply (hinit.seq (hscan.seq (hprep.seq (hc.seq hcleanup)))).mono
  simp only [localBudget]
  omega

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
