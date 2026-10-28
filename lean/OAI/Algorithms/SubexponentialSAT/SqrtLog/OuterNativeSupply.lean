import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeServiceBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeInitialBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionFinalInputs

namespace OAI.Algorithms

/-! The concrete native programs supply every exact observed history of the
actual initial-code execution. Constants and the cutoff precede all inputs. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafOuterProgram HashSelectProgram Filter
open scoped Topology
noncomputable section

 theorem exists_sparse_history (k qi : ℕ) :
    ∃ Ct At : ℝ, ∃ dt : ℕ, 1 ≤ Ct ∧ 0 ≤ At ∧ 0 < dt ∧
      ∀ᶠ n : ℕ in atTop,
      ∀ (F : OuterQuery.Formula n) B (nw Bw : List Bool),
      ExecSunflowerSearch.RawWidthAtMost k F →
      BinaryArithmetic.toNat nw=n → BinaryArithmetic.toNat Bw=B →
      0 < B → B ≤ Asymptotic.L n^qi → F.length ≤ n*B →
      F≠[] → [] ∉ F → ∀ a : Data,
      MainAdapter.CoreInput a (inputBits F) nw Bw →
      HistorySupply F B (LeafOuterNative.mass k) (LeafOuterNative.acceptedCount k) a
        (Execution.Final.tailCost Ct At dt n nw Bw (inputBits F)) := by
  obtain ⟨C,d,p,hinit⟩ := eventually_observed_initialCode_bound
  refine ⟨tailCoefficient k,tailExponent k qi,tailDegree k p,
    tailCoefficient_ge_one k,tailExponent_nonneg k qi,tailDegree_pos k p,?_⟩
  filter_upwards [hinit qi,eventually_native_history_services k qi C d p]
    with n hi hservices
  intro F B nw Bw hk hn hBval hB hBL hcount hne hno a hin ni z shifts code hei hz hshift hcode hrows hframe
  let W := (inputBits F).length+nw.length+Bw.length+1
  let V := W+CodeSetupOuterCost.setupMajorant C d qi n*(W+1)^p
  have hw : SubexpSetupStorage.WordBound W a := coreInput_wordBound hin
  have hcf := classified_stacks a (formulaRecords F)
  have hformula : a.stacks 784=Encoding.encodeList id (formulaRecords F) := by
    simp only [hin 784]; rfl
  have hm : 0 < (formulaRecords F).length := by
    simpa only [formulaRecords_length] using List.length_pos_iff.mpr hne
  have hrecords : formulaRecords F≠[] := List.length_pos_iff.mp hm
  have ha786 := hin 786
  have ha785 := hin 785
  norm_num at ha786 ha785
  have hob := hi (classified a (formulaRecords F)) W (formulaRecords F) B
    (by intro i; rw [hcf]; exact hw i)
    (by intro i hi; rw [hcf]; exact coreInput_empty hin i hi)
    (by rw [hcf]; exact hformula) hrecords hB
    (by rw [hcf,ha786]; exact hBval)
    (by rw [hcf,ha785]; exact hn)
    (by simpa only [formulaRecords_length] using hcount) hBL ni z hei
  have hzf : z.stacks 784=Encoding.encodeList id (formulaRecords F) :=
    (hframe 784 (by decide) (by decide)).trans hformula
  let P (m : ℕ) : Prop :=
    ∀ ready : StartReady z n m B, ∀ (s : SparseCode.SuppliedShifts m B)
      (Q : SparseCode.SuppliedLocal m B),
      z.stacks 777=candidateEncoding (LeafScopeResourceBounds.initialPayloads
        (z.stacks 768).length (CodeRowsProgram.serializedRows m s Q)) →
      ∃ svc : HistoryServices (formulaClauses F) (LeafOuterNative.mass k)
        (LeafOuterNative.acceptedCount k) z (LeafScopeResourceBounds.initialPayloads
          (z.stacks 768).length (CodeRowsProgram.serializedRows m s Q)),
        (svc.budget:ℝ) ≤ Statement.runtimeBound (tailCoefficient k) (tailExponent k qi)
          (tailDegree k p) W n
  have h0 : P (formulaRecords F).length := by
    intro ready s Q hr
    have hr' : z.stacks 777=candidateEncoding (OuterQuery.initial F z s Q) := by
      simpa only [OuterQuery.initial,ready.width] using hr
    have hh := hservices F B z ready hm hk hcount hB hBL hzf s Q hr' W V hob.2 le_rfl
    let Result (word : List Bool) : Prop :=
      ∃ svc : HistoryServices (formulaClauses F) (LeafOuterNative.mass k)
        (LeafOuterNative.acceptedCount k) z (LeafScopeResourceBounds.initialPayloads
          word.length (CodeRowsProgram.serializedRows (formulaRecords F).length s Q)),
        (svc.budget:ℝ) ≤ Statement.runtimeBound (tailCoefficient k) (tailExponent k qi)
          (tailDegree k p) W n
    have hh' : Result (z.stacks 783) := hh
    exact Eq.mp (congrArg Result ready.width) hh'
  have h1 : P F.length := (formulaRecords_length F) ▸ h0
  obtain ⟨svc,hsvc⟩ := h1 hz shifts code hrows
  refine ⟨svc,?_⟩
  have hh := hsvc.trans (Nat.le_ceil _)
  exact_mod_cast hh

end
end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
