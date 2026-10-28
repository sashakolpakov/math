import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramContext
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitializeLift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramContext
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramZero

namespace OAI.Algorithms

/-! Native readiness of the extracted source executor after the paid zero-array
initializer. The source dimension is the full count on210; no identification
with an earlier jet-length cache is made. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (ports physicalCfg contextStore)
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem context_value (s : LayoutSourceRowsProgram.Store) (i : Fin 256)
    (h26 : i ≠ 26) (h27 : i ≠ 27) (h28 : i ≠ 28) (h29 : i ≠ 29) :
    contextStore (executionContext s) i = s (executorPorts i) := by
  obtain ⟨j,rfl⟩ := ports.surjective i
  revert h26 h27 h28 h29
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro j
    fin_cases j
    · intro h _ _ _; exact False.elim (h (by decide))
    · intro _ _ h _; exact False.elim (h (by decide))
    · intro _ h _ _; exact False.elim (h (by decide))
    · intro _ _ _ h; exact False.elim (h (by decide))
  · intro j _ _ _ _
    exact SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_context _ _ _ _ _ _ _ _ j

theorem evaluation_value (s : LayoutSourceRowsProgram.Store) (i : Fin 256)
    (h21 : i ≠ 21) (h26 : i ≠ 26) (h27 : i ≠ 27) (h28 : i ≠ 28) (h29 : i ≠ 29) :
    contextStore (executionContext (evaluationInput s)) i = s (executorPorts i) := by
  rw [executionContext_evaluation, context_value _ i h26 h27 h28 h29]
  have hp : executorPorts i ≠ 21 := by
    intro he
    apply h21
    apply Fin.ext
    have hv := congrArg (fun j : Fin 340 => j.val) he
    change i.val = 21 at hv
    exact hv
  simp [hp]

theorem evaluation_empty21 (s : LayoutSourceRowsProgram.Store) :
    contextStore (executionContext (evaluationInput s)) 21 = [] := by
  rw [executionContext_evaluation, context_value _ 21 (by decide) (by decide)
    (by decide) (by decide)]
  simp [executorPorts]

theorem initialize_projection (s : LayoutSourceRowsProgram.Store) (D W : ℕ) :
    initializeFinish s D W ∘ executorPorts =
      LayoutSourceRowsProgramInitialize.finish (s ∘ executorPorts) D W := by
  funext i
  simp [initializeFinish,LayoutSourceRowsProgramInitialize.finish,
    Function.comp_def,executorPorts,Function.update_apply,Fin.ext_iff]

/-- The only ports hidden or changed by extraction and initialization. -/
def Preserved (i : Fin 256) : Prop :=
  i ≠ 21 ∧ i ≠ 26 ∧ i ≠ 27 ∧ i ≠ 28 ∧ i ≠ 29 ∧
    i ≠ 243 ∧ i ≠ 242 ∧ i ≠ 192 ∧ i ≠ 193

theorem initialized_value (s : LayoutSourceRowsProgram.Store) (D W : ℕ)
    (i : Fin 256) (hi : Preserved i) :
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) i =
      s (executorPorts i) := by
  rcases hi with ⟨h21,h26,h27,h28,h29,h243,h242,h192,h193⟩
  rw [evaluation_value _ i h21 h26 h27 h28 h29]
  have hp := congrFun (initialize_projection s D W) i
  change initializeFinish s D W (executorPorts i) = _ at hp
  rw [hp]
  exact LayoutSourceRowsProgramInitialize.finish_frame _ D W i h243 h242 h192 h193

theorem initialized_cache (s : LayoutSourceRowsProgram.Store) (D W : ℕ) :
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) 192 =
        List.replicate (D*W) false ∧
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) 193 =
        List.replicate D true ∧
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) 242 =
        List.replicate (D*W) false ∧
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) 243 =
        List.replicate D true := by
  repeat' constructor

/-- Empty physical work ports required in addition to native arithmetic. -/
structure Empty (s : LayoutSourceRowsProgram.Store) : Prop where
  empty99 : s (executorPorts 99) = []
  empty121 : s (executorPorts 121) = []
  empty122 : s (executorPorts 122) = []
  empty240 : s (executorPorts 240) = []
  empty241 : s (executorPorts 241) = []
  empty244 : s (executorPorts 244) = []
  empty245 : s (executorPorts 245) = []
  buffers : ∀ i, s (executorPorts (SubexpConvolutionControl.bufferPorts i)) = []

variable (p t : ℕ) [Fact p.Prime]
  (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
  {d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))

omit [Fact (Nat.Prime p)] in
theorem initialized_arithmetic (s : LayoutSourceRowsProgram.Store) (D W : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : DensePolynomialProgram.PairSpec.BaseReady p t M cache table
      (s ∘ executorPorts) width frame) :
    DensePolynomialProgram.PairSpec.BaseReady p t M cache table
      (contextStore (executionContext (evaluationInput (initializeFinish s D W)))) width frame := by
  constructor
  · intro i h8 h9
    rw [initialized_value s D W _
      ((by unfold Preserved; decide : ∀ j : Fin 32, Preserved (DensePolynomialProgram.RingCall.ports j)) i)]
    exact H.high i h8 h9
  · intro i
    rw [initialized_value s D W _
      ((by unfold Preserved; decide : ∀ j : Fin 20,
        Preserved (SubexpConvolutionPair.lowPort (SubexpJetCellProgram.scalarPorts j))) i)]
    exact H.low i
  · rw [initialized_value s D W 104 (by unfold Preserved; decide)]
    exact H.width
  · exact H.scalarWidthLength
  · rw [initialized_value s D W 204 (by unfold Preserved; decide)]
    exact H.degreeLength
  · rw [initialized_value s D W 120 (by unfold Preserved; decide)]
    exact H.scratch
  · intro i hlo hhi
    have hi : Preserved i := by
      unfold Preserved
      repeat' constructor
      all_goals intro he
      all_goals subst i
      all_goals omega
    rw [initialized_value s D W i hi]
    exact H.work i hlo hhi

theorem initialized_ready
    (ops : SubexpSymbolicCost.RingProgram (DensePolynomialProgram.Coeff (baseWidth p t) d))
    (hzero : RingProgram.flat ops.zeroRun.1 = List.replicate (d*baseWidth p t) false)
    (s : LayoutSourceRowsProgram.Store) (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (H : DensePolynomialProgram.PairSpec.BaseReady p t M cache table
      (s ∘ executorPorts) width frame) (E : Empty s) :
    PolynomialExecutorProgram.Ready p t M cache ops table D width frame
      (executionContext (evaluationInput (initializeFinish s D (d*baseWidth p t)))) := by
  constructor
  · exact initialized_arithmetic p t M cache table s D _ width frame H
  · exact evaluation_empty21 _
  · rw [initialized_value s D _ 99 (by unfold Preserved; decide)]; exact E.empty99
  · rw [initialized_value s D _ 121 (by unfold Preserved; decide)]; exact E.empty121
  · rw [initialized_value s D _ 122 (by unfold Preserved; decide)]; exact E.empty122
  · rw [initialized_value s D _ 240 (by unfold Preserved; decide)]; exact E.empty240
  · rw [initialized_value s D _ 241 (by unfold Preserved; decide)]; exact E.empty241
  · rw [initialized_value s D _ 244 (by unfold Preserved; decide)]; exact E.empty244
  · rw [initialized_value s D _ 245 (by unfold Preserved; decide)]; exact E.empty245
  · intro i
    rw [initialized_value s D _ _
      ((by unfold Preserved; decide : ∀ j, Preserved (SubexpConvolutionControl.bufferPorts j)) i)]
    exact E.buffers i
  · rw [(initialized_cache s D _).1]
    exact (LayoutSourceRowsProgramInitialize.encode_zero_array ops.zeroRun.1 hzero D).symm
  · rw [(initialized_cache s D _).2.1]
    simp
  · rw [(initialized_cache s D _).2.2.1]
    exact (LayoutSourceRowsProgramInitialize.encode_zero_array ops.zeroRun.1 hzero D).symm

theorem source_dimension_preserved (s : LayoutSourceRowsProgram.Store) (D W : ℕ) :
    contextStore (executionContext (evaluationInput (initializeFinish s D W))) 210 = s 210 := by
  simpa [executorPorts] using initialized_value s D W 210 (by unfold Preserved; decide)

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness

end OAI.Algorithms
